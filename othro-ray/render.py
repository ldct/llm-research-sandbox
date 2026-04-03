#!/usr/bin/env python3
"""Orthographic path tracer with proper materials (RT in a Weekend style)."""

import numpy as np
from PIL import Image
import time, sys, math, os
import multiprocessing as mp

rng = np.random.default_rng(42)

def _worker_init(seed):
    global rng
    rng = np.random.default_rng(seed)

# ── Vector helpers ──
def normalize(v):
    n = np.linalg.norm(v)
    return v / n if n > 1e-12 else v

def reflect(v, n):
    return v - 2.0 * np.dot(v, n) * n

def refract(uv, n, etai_over_etat):
    cos_theta = min(np.dot(-uv, n), 1.0)
    r_out_perp = etai_over_etat * (uv + cos_theta * n)
    r_out_parallel = -math.sqrt(abs(1.0 - np.dot(r_out_perp, r_out_perp))) * n
    return r_out_perp + r_out_parallel

def schlick(cosine, ref_idx):
    r0 = ((1 - ref_idx) / (1 + ref_idx)) ** 2
    return r0 + (1 - r0) * (1 - cosine) ** 5

def random_unit_vector():
    while True:
        p = rng.uniform(-1, 1, 3)
        if np.dot(p, p) < 1.0:
            return normalize(p)

def random_in_hemisphere(normal):
    v = random_unit_vector()
    if np.dot(v, normal) < 0:
        v = -v
    return v

# ── Batch vector helpers ──
def random_unit_vectors_batch(N):
    """Generate N unit vectors using normal distribution (no rejection needed)."""
    p = rng.standard_normal((N, 3))
    return p / np.linalg.norm(p, axis=1, keepdims=True)

def normalize_batch(v):
    return v / np.linalg.norm(v, axis=1, keepdims=True)

def sky_color_batch(ray_ds):
    """Vectorized sky color for (N,3) ray directions."""
    d = normalize_batch(ray_ds)
    t = 0.5 * (d[:, 1:2] + 1.0)
    bottom = np.array([0.85, 0.88, 0.75])
    top    = np.array([0.65, 0.85, 0.72])
    sky = bottom * (1 - t) + top * t
    sun_dir = normalize(np.array([-0.4, 0.8, -0.3]))
    sun_dot = np.maximum(0.0, d @ sun_dir)
    sky += np.array([1.0, 0.95, 0.85]) * (sun_dot[:, None] ** 64) * 2.0
    sky += np.array([1.0, 0.97, 0.90]) * (sun_dot[:, None] ** 8) * 0.3
    return sky

# ── Materials (RT in a Weekend style) ──
class Lambertian:
    def __init__(self, albedo):
        self.albedo = np.array(albedo, dtype=np.float64)

    def scatter(self, ray_d, hit_p, normal):
        scatter_dir = normal + random_unit_vector()
        if np.linalg.norm(scatter_dir) < 1e-8:
            scatter_dir = normal
        return normalize(scatter_dir), self.albedo

    def scatter_batch(self, ray_ds, normals):
        """Returns (scatter_dirs, attenuations, valid_mask) for N rays."""
        N = len(normals)
        dirs = normals + random_unit_vectors_batch(N)
        norms = np.linalg.norm(dirs, axis=1, keepdims=True)
        degenerate = (norms < 1e-8)[:, 0]
        dirs[degenerate] = normals[degenerate]
        dirs = dirs / np.linalg.norm(dirs, axis=1, keepdims=True)
        return dirs, np.tile(self.albedo, (N, 1)), np.ones(N, dtype=bool)


class Metal:
    def __init__(self, albedo, fuzz=0.0):
        self.albedo = np.array(albedo, dtype=np.float64)
        self.fuzz = min(fuzz, 1.0)

    def scatter(self, ray_d, hit_p, normal):
        reflected = reflect(normalize(ray_d), normal)
        scattered = reflected + self.fuzz * random_unit_vector()
        scattered = normalize(scattered)
        if np.dot(scattered, normal) > 0:
            return scattered, self.albedo
        return None, None

    def scatter_batch(self, ray_ds, normals):
        N = len(normals)
        ud = normalize_batch(ray_ds)
        dot_vn = np.einsum('ij,ij->i', ud, normals)[:, None]
        reflected = ud - 2.0 * dot_vn * normals
        scattered = reflected + self.fuzz * random_unit_vectors_batch(N)
        scattered = normalize_batch(scattered)
        valid = np.einsum('ij,ij->i', scattered, normals) > 0
        return scattered, np.tile(self.albedo, (N, 1)), valid


class Dielectric:
    def __init__(self, ior, tint=None):
        self.ior = ior
        self.tint = np.array(tint if tint else [1,1,1], dtype=np.float64)

    def scatter(self, ray_d, hit_p, normal):
        ud = normalize(ray_d)
        front_face = np.dot(ud, normal) < 0
        n = normal if front_face else -normal
        ratio = 1.0/self.ior if front_face else self.ior
        cos_theta = min(np.dot(-ud, n), 1.0)
        sin_theta = math.sqrt(1.0 - cos_theta*cos_theta)
        cannot_refract = ratio * sin_theta > 1.0
        if cannot_refract or schlick(cos_theta, ratio) > rng.random():
            direction = reflect(ud, n)
        else:
            direction = refract(ud, n, ratio)
        return normalize(direction), self.tint

    def scatter_batch(self, ray_ds, normals):
        N = len(normals)
        ud = normalize_batch(ray_ds)
        dot_udn = np.einsum('ij,ij->i', ud, normals)
        front = dot_udn < 0
        n = np.where(front[:, None], normals, -normals)
        ratio = np.where(front, 1.0 / self.ior, self.ior)

        cos_theta = np.minimum(np.einsum('ij,ij->i', -ud, n), 1.0)
        sin_theta = np.sqrt(np.maximum(1.0 - cos_theta**2, 0))
        cannot_refract = ratio * sin_theta > 1.0

        r0 = ((1 - self.ior) / (1 + self.ior)) ** 2
        schlick_v = r0 + (1 - r0) * (1 - cos_theta) ** 5
        use_reflect = cannot_refract | (schlick_v > rng.random(N))

        # Refraction
        cos_c = cos_theta[:, None]
        ratio_c = ratio[:, None]
        r_perp = ratio_c * (ud + cos_c * n)
        perp_sq = np.einsum('ij,ij->i', r_perp, r_perp)
        r_para = -np.sqrt(np.maximum(1.0 - perp_sq, 0))[:, None] * n
        refracted = r_perp + r_para

        # Reflection
        dot_vn = np.einsum('ij,ij->i', ud, n)[:, None]
        reflected = ud - 2.0 * dot_vn * n

        direction = np.where(use_reflect[:, None], reflected, refracted)
        direction = normalize_batch(direction)
        return direction, np.tile(self.tint, (N, 1)), np.ones(N, dtype=bool)


# ── Shapes ──
class Sphere:
    def __init__(self, center, radius, material, depth_shift=0.0):
        self.center = np.array(center, dtype=np.float64)
        self.radius = radius
        self.material = material
        self.depth_shift = depth_shift

    def hit(self, ray_o, ray_d, t_min=0.001, t_max=1e18):
        oc = ray_o - self.center
        a = np.dot(ray_d, ray_d)
        half_b = np.dot(oc, ray_d)
        c = np.dot(oc, oc) - self.radius**2
        disc = half_b*half_b - a*c
        if disc < 0: return None
        sqrtd = math.sqrt(disc)
        t = (-half_b - sqrtd) / a
        if t < t_min or t > t_max:
            t = (-half_b + sqrtd) / a
            if t < t_min or t > t_max: return None
        p = ray_o + ray_d * t
        n = (p - self.center) / self.radius
        return (t, t + self.depth_shift, p, n, self.material)

    def hit_batch(self, ray_os, ray_ds, t_min=0.001, t_max=1e18):
        N = len(ray_os)
        oc = ray_os - self.center
        a = np.einsum('ij,ij->i', ray_ds, ray_ds)
        half_b = np.einsum('ij,ij->i', oc, ray_ds)
        c = np.einsum('ij,ij->i', oc, oc) - self.radius**2
        disc = half_b*half_b - a*c

        res_t = np.full(N, 1e18)
        res_sort_t = np.full(N, 1e18)
        res_p = np.zeros((N, 3))
        res_n = np.zeros((N, 3))

        valid = disc >= 0
        if not valid.any():
            return res_t, res_sort_t, res_p, res_n

        sqrtd = np.sqrt(np.maximum(disc[valid], 0))
        av, hbv = a[valid], half_b[valid]
        t1 = (-hbv - sqrtd) / av
        t2 = (-hbv + sqrtd) / av
        t = np.where((t1 >= t_min) & (t1 <= t_max), t1,
            np.where((t2 >= t_min) & (t2 <= t_max), t2, 1e18))

        hit = t < 1e18
        vi = np.where(valid)[0][hit]
        if not hit.any():
            return res_t, res_sort_t, res_p, res_n

        t_hit = t[hit]
        p_hit = ray_os[vi] + ray_ds[vi] * t_hit[:, None]
        n_hit = (p_hit - self.center) / self.radius
        res_t[vi] = t_hit
        res_sort_t[vi] = t_hit + self.depth_shift
        res_p[vi] = p_hit
        res_n[vi] = n_hit
        return res_t, res_sort_t, res_p, res_n


class Box:
    def __init__(self, center, half_size, material, depth_shift=0.0):
        c = np.array(center, dtype=np.float64)
        h = np.array(half_size, dtype=np.float64)
        self.bmin = c - h
        self.bmax = c + h
        self.material = material
        self.depth_shift = depth_shift

    def hit(self, ray_o, ray_d, t_min=0.001, t_max=1e18):
        inv_d = np.where(np.abs(ray_d) > 1e-12, 1.0/ray_d, np.sign(ray_d)*1e12)
        t1 = (self.bmin - ray_o) * inv_d
        t2 = (self.bmax - ray_o) * inv_d
        tmin = np.minimum(t1, t2)
        tmax = np.maximum(t1, t2)
        tn = np.max(tmin)
        tf = np.min(tmax)
        if tn > tf or tf < t_min: return None
        t = tn if tn >= t_min else tf
        if t > t_max: return None
        p = ray_o + ray_d * t
        eps = 1e-4
        normal = np.array([0.0, 0.0, 0.0])
        for axis in range(3):
            if abs(p[axis] - self.bmin[axis]) < eps:
                normal[axis] = -1.0; break
            if abs(p[axis] - self.bmax[axis]) < eps:
                normal[axis] = 1.0; break
        return (t, t + self.depth_shift, p, normal, self.material)

    def hit_batch(self, ray_os, ray_ds, t_min=0.001, t_max=1e18):
        N = len(ray_os)
        safe_d = np.where(np.abs(ray_ds) > 1e-12, ray_ds, np.sign(ray_ds) * 1e-12)
        inv_d = 1.0 / safe_d
        t1 = (self.bmin - ray_os) * inv_d
        t2 = (self.bmax - ray_os) * inv_d
        tmin_v = np.minimum(t1, t2)
        tmax_v = np.maximum(t1, t2)
        tn = np.max(tmin_v, axis=1)
        tf = np.min(tmax_v, axis=1)

        valid = (tn <= tf) & (tf >= t_min)
        t = np.where(tn >= t_min, tn, tf)
        valid &= (t <= t_max)

        res_t = np.full(N, 1e18)
        res_sort_t = np.full(N, 1e18)
        res_p = np.zeros((N, 3))
        res_n = np.zeros((N, 3))

        if not valid.any():
            return res_t, res_sort_t, res_p, res_n

        vi = np.where(valid)[0]
        t_hit = t[vi]
        p_hit = ray_os[vi] + ray_ds[vi] * t_hit[:, None]

        eps = 1e-4
        n_hit = np.zeros((len(vi), 3))
        set_mask = np.zeros(len(vi), dtype=bool)
        for axis in range(3):
            near_min = (~set_mask) & (np.abs(p_hit[:, axis] - self.bmin[axis]) < eps)
            n_hit[near_min, axis] = -1.0
            set_mask |= near_min
            near_max = (~set_mask) & (np.abs(p_hit[:, axis] - self.bmax[axis]) < eps)
            n_hit[near_max, axis] = 1.0
            set_mask |= near_max

        res_t[vi] = t_hit
        res_sort_t[vi] = t_hit + self.depth_shift
        res_p[vi] = p_hit
        res_n[vi] = n_hit
        return res_t, res_sort_t, res_p, res_n


# ── Scene ──
def make_scene():
    objects = []

    # Materials
    M_WALL   = Lambertian([0.72, 0.80, 0.85])
    M_CREAM  = Lambertian([0.93, 0.90, 0.82])
    M_TEAL   = Metal([0.45, 0.85, 0.80], fuzz=0.05)  # shiny water
    M_GOLD   = Metal([0.85, 0.75, 0.30], fuzz=0.15)   # brushed gold
    M_MAUVE  = Lambertian([0.55, 0.30, 0.40])
    M_DARK   = Lambertian([0.08, 0.06, 0.07])
    M_OLIVE  = Lambertian([0.45, 0.55, 0.18])
    M_ORANGE = Lambertian([0.95, 0.50, 0.15])
    M_STAIRS = Lambertian([0.76, 0.72, 0.66])
    M_MIRROR = Metal([0.95, 0.95, 0.97], fuzz=0.0)    # perfect mirror
    M_GLASS  = Dielectric(1.5, tint=[0.95, 0.98, 1.0])
    M_WHITE  = Lambertian([0.95, 0.95, 0.95])
    M_PINK   = Metal([0.92, 0.45, 0.50], fuzz=0.1)
    M_COPPER = Metal([0.85, 0.55, 0.40], fuzz=0.25)

    def box(c, h, m, ds=0.0, depth_shift=None):
        objects.append(Box(c, h, m, depth_shift if depth_shift is not None else ds))
    def sphere(c, r, m, ds=0.0, depth_shift=None):
        objects.append(Sphere(c, r, m, depth_shift if depth_shift is not None else ds))

    # Ground
    box([0, -0.5, 0], [6.5, 0.3, 6.5], M_OLIVE)
    box([0, -0.1, 0], [5.5, 0.15, 5.5], M_CREAM)

    # ── LEFT TOWER ──
    LX, LZ = -3.5, 1.0
    box([LX, 2.0, LZ], [1.4, 2.0, 1.4], M_WALL)
    box([LX, 4.1, LZ], [1.55, 0.12, 1.55], M_CREAM)
    box([LX, 5.5, LZ], [1.1, 1.3, 1.1], M_WALL)
    box([LX, 6.9, LZ], [1.2, 0.12, 1.2], M_CREAM)
    box([LX, 7.8, LZ], [0.8, 0.8, 0.8], M_WALL)
    box([LX, 8.75, LZ], [0.9, 0.12, 0.9], M_CREAM)
    sphere([LX, 9.6, LZ], 0.7, M_GOLD)
    box([LX, 1.8, LZ+1.4], [0.55, 1.0, 0.12], M_DARK)
    box([LX, 5.6, LZ+1.1], [0.5, 0.6, 0.06], M_DARK)
    box([LX-1.42, 2.5, LZ], [0.06, 0.35, 0.25], M_MAUVE)
    box([LX-1.42, 5.8, LZ], [0.06, 0.28, 0.2], M_MAUVE)

    # ── RIGHT TOWER ──
    RX, RZ = 3.5, -1.0
    box([RX, 2.0, RZ], [1.2, 2.0, 1.2], M_WALL)
    box([RX, 4.1, RZ], [1.35, 0.12, 1.35], M_CREAM)
    box([RX, 5.3, RZ], [0.9, 1.1, 0.9], M_WALL)
    box([RX, 6.5, RZ], [1.0, 0.12, 1.0], M_CREAM)
    box([RX, 7.2, RZ], [0.65, 0.6, 0.65], M_WALL)
    box([RX, 7.95, RZ], [0.75, 0.12, 0.75], M_CREAM)
    sphere([RX, 8.6, RZ], 0.55, M_GOLD)
    box([RX, 1.7, RZ-1.22], [0.45, 0.9, 0.06], M_DARK)
    box([RX+1.22, 2.5, RZ], [0.06, 0.35, 0.22], M_MAUVE)
    box([RX+1.22, 5.6, RZ], [0.06, 0.28, 0.18], M_MAUVE)

    # ── MIDDLE STRUCTURE ──
    MX, MZ = 0.0, 0.0
    box([MX, 1.5, MZ], [1.0, 1.5, 1.0], M_WALL)
    box([MX, 3.1, MZ], [1.1, 0.12, 1.1], M_CREAM)
    box([MX, 4.0, MZ], [0.7, 0.8, 0.7], M_WALL)
    box([MX, 4.9, MZ], [0.8, 0.1, 0.8], M_CREAM)
    box([MX, 1.2, MZ+1.02], [0.4, 0.7, 0.06], M_DARK)

    # ── BRIDGES ──
    bx1 = (LX + MX) / 2; bz1 = (LZ + MZ) / 2
    box([bx1, 4.2, bz1], [2.2, 0.18, 0.6], M_CREAM)
    box([bx1, 4.55, bz1-0.5], [2.2, 0.18, 0.08], M_WALL)
    bx2 = (MX + RX) / 2; bz2 = (MZ + RZ) / 2
    box([bx2, 3.2, bz2], [2.2, 0.18, 0.6], M_CREAM)
    box([bx2, 3.55, bz2-0.5], [2.2, 0.18, 0.08], M_WALL)

    # ── WATER (shiny metal-teal) ──
    box([bx1, 6.8, LZ-0.5], [2.0, 0.08, 0.4], M_TEAL)
    box([MX+0.5, 5.5, MZ-0.3], [0.3, 1.3, 0.3], M_TEAL)
    box([bx2, 4.15, bz2], [2.0, 0.08, 0.4], M_TEAL, depth_shift=-4.0)

    # ── STAIRS ──
    for i in range(12):
        box([LX+1.4, 0.15+i*0.33, LZ+i*0.12], [0.35, 0.1, 0.22], M_STAIRS)
    for i in range(9):
        box([RX-1.2, 0.15+i*0.38, RZ-i*0.1], [0.22, 0.1, 0.35], M_STAIRS)
    # Impossible staircase
    for i in range(8):
        box([RX-i*0.85, 3.3, RZ-i*0.85], [0.35, 0.1, 0.3], M_STAIRS, depth_shift=i*1.0)

    # ── GLASS SPHERE (refraction!) ──
    sphere([MX, 5.3, MZ], 0.35, M_GLASS)

    # ── MIRROR SPHERE ──
    sphere([bx1+0.5, 4.65, bz1+0.3], 0.25, M_MIRROR)

    # ── COPPER SPHERE ──
    sphere([bx2-0.3, 3.6, bz2+0.3], 0.2, M_COPPER)

    # ── Orange geometric accent ──
    sphere([LX+1.0, 7.0, LZ+1.0], 0.25, M_ORANGE)

    # ── Character ──
    box([bx2, 3.6, bz2+0.2], [0.1, 0.2, 0.1], M_ORANGE)
    sphere([bx2, 3.9, bz2+0.2], 0.09, M_WHITE)

    # ── Pillars ──
    for x, z in [(-4, 3), (-1, 4.5), (3, 4.5), (4.5, -1), (-4, -4)]:
        box([x, -0.1, z], [0.3, 0.5, 0.3], M_WALL)
        box([x, -0.3, z], [0.18, 0.35, 0.08], M_DARK)

    # ── Plants ──
    sphere([bx1, 4.6, bz1+0.4], 0.2, M_OLIVE)
    sphere([bx2+0.5, 3.55, bz2+0.4], 0.18, M_OLIVE)
    sphere([MX-0.8, 3.4, MZ+0.8], 0.15, M_OLIVE)

    # ── Flagpole tips ──
    sphere([LX, 10.5, LZ], 0.09, M_PINK)
    sphere([RX, 9.3, RZ], 0.08, M_PINK)

    return objects

# ── Sky / environment light ──
def sky_color(ray_d):
    """Gradient sky that acts as the scene's light source."""
    d = normalize(ray_d)
    # Blend from bottom (warm) to top (mint) with a bright upper region
    t = 0.5 * (d[1] + 1.0)
    bottom = np.array([0.85, 0.88, 0.75])
    top    = np.array([0.65, 0.85, 0.72])
    sky = bottom * (1 - t) + top * t
    # Add a sun-like bright area in the upper-left
    sun_dir = normalize(np.array([-0.4, 0.8, -0.3]))
    sun_dot = max(0.0, np.dot(d, sun_dir))
    sky += np.array([1.0, 0.95, 0.85]) * (sun_dot ** 64) * 2.0  # sharp sun highlight
    sky += np.array([1.0, 0.97, 0.90]) * (sun_dot ** 8) * 0.3   # soft sun glow
    return sky

# ── Path tracer (scalar) ──
def trace(ray_o, ray_d, scene, depth=0, max_depth=6):
    if depth >= max_depth:
        return np.zeros(3)

    # Find closest hit
    best = None
    best_sort_t = 1e18
    for obj in scene:
        result = obj.hit(ray_o, ray_d)
        if result is not None:
            t, sort_t, p, n, mat = result
            if sort_t < best_sort_t:
                best_sort_t = sort_t
                best = (t, p, n, mat)

    if best is None:
        return sky_color(ray_d)

    t, p, n, mat = best

    # Make sure normal faces against ray
    if np.dot(ray_d, n) > 0 and not isinstance(mat, Dielectric):
        n = -n

    scattered_dir, attenuation = mat.scatter(ray_d, p, n)
    if scattered_dir is None:
        return np.zeros(3)

    # Recurse
    incoming = trace(p + n * 0.001 if np.dot(scattered_dir, n) > 0 else p - n * 0.001,
                     scattered_dir, scene, depth + 1, max_depth)
    return attenuation * incoming

# ── Vectorized path tracer ──
def trace_vectorized(ray_os, ray_ds, scene, max_depth=6):
    """Trace N rays simultaneously using NumPy vectorization."""
    N = len(ray_os)
    colors = np.zeros((N, 3))
    throughput = np.ones((N, 3))
    active = np.ones(N, dtype=bool)
    curr_o = ray_os.copy()
    curr_d = ray_ds.copy()

    for depth in range(max_depth):
        if not active.any():
            break

        ao = curr_o[active]
        ad = curr_d[active]
        n_active = len(ao)

        best_t = np.full(n_active, 1e18)
        best_sort_t = np.full(n_active, 1e18)
        best_p = np.zeros((n_active, 3))
        best_n = np.zeros((n_active, 3))
        best_obj_idx = np.full(n_active, -1, dtype=int)

        for obj_idx, obj in enumerate(scene):
            t, sort_t, p, n = obj.hit_batch(ao, ad)
            better = sort_t < best_sort_t
            best_t = np.where(better, t, best_t)
            best_sort_t = np.where(better, sort_t, best_sort_t)
            best_p[better] = p[better]
            best_n[better] = n[better]
            best_obj_idx[better] = obj_idx

        active_idx = np.where(active)[0]

        # Rays that missed -> sky color, deactivate
        missed = best_sort_t >= 1e18
        if missed.any():
            g_missed = active_idx[missed]
            colors[g_missed] += throughput[g_missed] * sky_color_batch(ad[missed])
            active[g_missed] = False

        hit_mask = ~missed
        if not hit_mask.any():
            continue

        g_hit = active_idx[hit_mask]
        h_ray_d = ad[hit_mask]
        h_p = best_p[hit_mask]
        h_n = best_n[hit_mask]
        h_obj_idx = best_obj_idx[hit_mask]

        new_d = np.zeros_like(h_ray_d)
        new_atten = np.ones((len(g_hit), 3))
        ray_valid = np.zeros(len(g_hit), dtype=bool)

        # Group rays by material instance and scatter
        for obj_idx in np.unique(h_obj_idx):
            mat = scene[obj_idx].material
            mask = h_obj_idx == obj_idx

            sub_d = h_ray_d[mask]
            sub_n = h_n[mask].copy()

            # Flip normals to face ray (non-dielectric only)
            if not isinstance(mat, Dielectric):
                flip = np.einsum('ij,ij->i', sub_d, sub_n) > 0
                sub_n[flip] = -sub_n[flip]
                h_n[mask] = sub_n  # write back for offset calc

            scat_d, atten, valid = mat.scatter_batch(sub_d, sub_n)
            new_d[mask] = scat_d
            new_atten[mask] = atten
            ray_valid[mask] = valid

        throughput[g_hit] *= new_atten

        # Offset origins to avoid self-intersection
        dot_new_n = np.einsum('ij,ij->i', new_d, h_n)
        offset = np.where(dot_new_n[:, None] > 0, h_n, -h_n) * 0.001
        curr_o[g_hit] = h_p + offset
        curr_d[g_hit] = new_d

        # Deactivate rays absorbed by metal (scattered behind surface)
        g_invalid = g_hit[~ray_valid]
        active[g_invalid] = False

    return colors


def _camera_setup(width, height):
    angle_y = np.radians(45)
    angle_x = np.radians(30)
    ray_dir = normalize(np.array([
        math.sin(angle_y) * math.cos(angle_x),
        -math.sin(angle_x),
        math.cos(angle_y) * math.cos(angle_x),
    ]))
    world_up = np.array([0.0, 1.0, 0.0])
    cam_right = normalize(np.cross(ray_dir, world_up))
    cam_up = normalize(np.cross(cam_right, ray_dir))
    return ray_dir, cam_right, cam_up


def render_vectorized(width=80, height=100, spp=32, outfile='impossible_vec.png'):
    scene = make_scene()
    ray_dir, cam_right, cam_up = _camera_setup(width, height)
    ortho_size = 14.0
    aspect = width / height

    print(f"[vectorized] Rendering {width}x{height}, {spp} spp, {len(scene)} objects, max_depth=6...")
    t0 = time.time()

    # Generate all H*W*spp rays at once
    jx = rng.random((height, width, spp)) - 0.5
    jy = rng.random((height, width, spp)) - 0.5
    py_idx = np.arange(height)[:, None, None]
    px_idx = np.arange(width)[None, :, None]
    u = ((px_idx + jx) / width - 0.5) * ortho_size * aspect
    v = (0.5 - (py_idx + jy) / height) * ortho_size

    base_o = np.array([-8.0, 12.0, -8.0])
    ray_os = base_o + u[..., None] * cam_right + v[..., None] * cam_up  # (H,W,spp,3)

    N = height * width * spp
    ray_os_flat = ray_os.reshape(N, 3)
    ray_ds_flat = np.broadcast_to(ray_dir, (N, 3)).copy()

    colors_flat = trace_vectorized(ray_os_flat, ray_ds_flat, scene)

    img = colors_flat.reshape(height, width, spp, 3).mean(axis=2)
    elapsed = time.time() - t0
    print(f"[vectorized] Done in {elapsed:.1f}s")

    img = np.clip(img, 0, 1)
    img = np.power(img, 1.0 / 2.2)
    Image.fromarray((img * 255).astype(np.uint8)).save(outfile)
    print(f'Saved {outfile}')
    return elapsed


def _render_rows(args):
    row_start, row_end, width, height, spp = args
    scene = make_scene()
    ray_dir, cam_right, cam_up = _camera_setup(width, height)
    ortho_size = 14.0
    aspect = width / height

    chunk = np.zeros((row_end - row_start, width, 3), dtype=np.float64)
    for py in range(row_start, row_end):
        for px in range(width):
            col = np.zeros(3)
            for s in range(spp):
                jx = rng.random() - 0.5
                jy = rng.random() - 0.5
                u = ((px + jx) / width - 0.5) * ortho_size * aspect
                v = (0.5 - (py + jy) / height) * ortho_size
                ray_o = np.array([-8.0, 12.0, -8.0]) + cam_right * u + cam_up * v
                col += trace(ray_o, ray_dir, scene)
            chunk[py - row_start, px] = col / spp
    return row_start, chunk


def render(width=80, height=100, spp=32, outfile='impossible.png'):
    scene = make_scene()
    ncores = os.cpu_count() or 1
    print(f"[multicore]  Rendering {width}x{height}, {spp} spp, {len(scene)} objects, max_depth=6, {ncores} cores...")
    t0 = time.time()

    rows_per_chunk = max(1, height // ncores)
    chunks = []
    row = 0
    for i in range(ncores):
        r_end = row + rows_per_chunk if i < ncores - 1 else height
        chunks.append((row, r_end, width, height, spp))
        row = r_end
        if row >= height:
            break

    img = np.zeros((height, width, 3), dtype=np.float64)
    with mp.Pool(ncores, initializer=_worker_init, initargs=(42,)) as pool:
        results = pool.map(_render_rows, chunks)
    for row_start, chunk in results:
        img[row_start:row_start + chunk.shape[0]] = chunk

    elapsed = time.time() - t0
    print(f"[multicore]  Done in {elapsed:.1f}s")

    img = np.clip(img, 0, 1)
    img = np.power(img, 1.0 / 2.2)
    Image.fromarray((img * 255).astype(np.uint8)).save(outfile)
    print(f'Saved {outfile}')
    return elapsed


if __name__ == '__main__':
    W, H, SPP = 80, 100, 32
    t_vec = render_vectorized(W, H, SPP, 'impossible_vec.png')
    t_mc  = render(W, H, SPP, 'impossible_mc.png')
    print(f"\nSpeedup: {t_mc/t_vec:.2f}x  (vectorized vs multicore)")
