"""Shared physically based modeling helpers for the Monument Valley studies."""
import json
import math
import random
from pathlib import Path
import bpy
from mathutils import Vector, noise
from mathutils.geometry import convex_hull_2d
ROOT = Path(__file__).resolve().parents[1]
scene = bpy.context.scene
manifest = json.loads((ROOT / 'assets/textures/manifest.json').read_text())
DIRECTION = Vector((1, -1, 1.2)).normalized()
CUBE_FACES = [(0,1,2,3),(4,7,6,5),(0,4,5,1),(1,5,6,2),(2,6,7,3),(3,7,4,0)]
STAIR_FLIGHTS = []
COLLISION_AUDITS = []
def basic(name, color, roughness=.5, metallic=0):
    m = bpy.data.materials.new(name)
    m.use_nodes = True
    p = m.node_tree.nodes.get('Principled BSDF')
    p.inputs['Base Color'].default_value = (*color, 1)
    p.inputs['Roughness'].default_value = roughness
    p.inputs['Metallic'].default_value = metallic
    return m

def scanned(name, asset, scale, roughness_factor=1):
    m = basic(name, (.55, .5, .4))
    n, l = m.node_tree.nodes, m.node_tree.links
    p = n.get('Principled BSDF')
    coord = n.new('ShaderNodeTexCoord')
    mapping = n.new('ShaderNodeVectorMath')
    mapping.operation = 'SCALE'
    mapping.inputs[3].default_value = scale
    l.new(coord.outputs['Object'], mapping.inputs[0])
    anchor = bpy.data.objects.get('Texture space')
    if not anchor:
        anchor = bpy.data.objects.new('Texture space', None)
        scene.collection.objects.link(anchor)
    coord.object = anchor
    if asset not in manifest:
        return m
    maps = {}
    for key in ('Diffuse', 'Rough', 'Displacement'):
        tex = n.new('ShaderNodeTexImage')
        tex.image = bpy.data.images.load(str(ROOT / manifest[asset][key]), check_existing=True)
        if key != 'Diffuse':
            tex.image.colorspace_settings.name = 'Non-Color'
        tex.projection = 'BOX'
        tex.projection_blend = .15
        l.new(mapping.outputs['Vector'], tex.inputs['Vector'])
        maps[key] = tex
    l.new(maps['Diffuse'].outputs['Color'], p.inputs['Base Color'])
    rough = n.new('ShaderNodeMath')
    rough.operation = 'MULTIPLY'
    rough.inputs[1].default_value = roughness_factor
    l.new(maps['Rough'].outputs['Color'], rough.inputs[0])
    l.new(rough.outputs[0], p.inputs['Roughness'])
    bump = n.new('ShaderNodeBump')
    bump.inputs['Strength'].default_value = .25
    bump.inputs['Distance'].default_value = .018 if asset != 'marble_01' else .004
    l.new(maps['Displacement'].outputs['Color'], bump.inputs['Height'])
    l.new(bump.outputs['Normal'], p.inputs['Normal'])
    return m

def mesh(name, verts, faces, mat, bevel=0):
    data = bpy.data.meshes.new(name)
    data.from_pydata(verts, [], faces)
    data.update()
    obj = bpy.data.objects.new(name, data)
    scene.collection.objects.link(obj)
    if mat:
        data.materials.append(mat)
    if bevel:
        mod = obj.modifiers.new('Dressed edges', 'BEVEL')
        mod.width = bevel
        mod.segments = 3
        mod = obj.modifiers.new('Weighted surface normals', 'WEIGHTED_NORMAL')
    return obj

def box(name, loc, dims, mat, bevel=.012):
    bpy.ops.mesh.primitive_cube_add(size=1, location=loc)
    o = bpy.context.object
    o.name = name
    o.dimensions = dims
    bpy.ops.object.transform_apply(location=False, rotation=False, scale=True)
    o.data.materials.append(mat)
    if bevel:
        b = o.modifiers.new('Dressed edges', 'BEVEL')
        b.width = bevel
        b.segments = 3
        o.modifiers.new('Weighted normals', 'WEIGHTED_NORMAL')
    return o

def rod(name, a, b, radius, mat):
    a, b = Vector(a), Vector(b)
    d = b - a
    bpy.ops.mesh.primitive_cylinder_add(vertices=16, radius=radius, depth=d.length, location=(a+b)/2)
    o = bpy.context.object
    o.name = name
    o.rotation_euler = d.to_track_quat('Z', 'Y').to_euler()
    o.data.materials.append(mat)
    for poly in o.data.polygons: poly.use_smooth = True
    return o

def area(name, pos, target, power, color, size, size_y=None):
    data = bpy.data.lights.new(name, 'AREA')
    data.energy, data.color = power, color
    data.shape = 'RECTANGLE' if size_y else 'DISK'
    data.size = size
    if size_y: data.size_y = size_y
    o = bpy.data.objects.new(name, data)
    scene.collection.objects.link(o)
    o.location = pos
    o.rotation_euler = (Vector(target)-o.location).to_track_quat('-Z', 'Y').to_euler()
    return o


def setup(preview=False, samples=512, portrait=True):
    random.seed(81)
    bpy.ops.object.select_all(action='SELECT')
    bpy.ops.object.delete(use_global=False)
    scene.render.engine = 'CYCLES'
    scene.cycles.samples = 48 if preview else samples
    scene.cycles.use_denoising = True
    scene.cycles.adaptive_threshold = .028 if preview else .007
    scene.cycles.max_bounces = 16
    scene.cycles.diffuse_bounces = 6
    scene.cycles.glossy_bounces = 8
    scene.cycles.transmission_bounces = 12
    scene.cycles.seed = 39
    try:
        prefs = bpy.context.preferences.addons['cycles'].preferences
        prefs.compute_device_type = 'METAL'
        prefs.get_devices()
        for device in prefs.devices:
            device.use = device.type == 'METAL'
        scene.cycles.device = 'GPU'
    except Exception as e:
        print('CPU fallback:', e)
    scene.render.resolution_x = 960 if preview else 2400
    scene.render.resolution_y = (1120 if preview else 2800) if portrait else (960 if preview else 2400)
    scene.render.resolution_percentage = 100
    scene.render.image_settings.file_format = 'PNG'
    scene.render.image_settings.color_mode = 'RGB'
    scene.render.image_settings.color_depth = '16'
    scene.view_settings.view_transform = 'AgX'
    scene.view_settings.look = 'AgX - Medium High Contrast'
    scene.view_settings.exposure = -1
    scene.unit_settings.system = 'METRIC'


def tint(material, color, factor=1, multiply=True, roughness=None):
    n, l = material.node_tree.nodes, material.node_tree.links
    p = n.get('Principled BSDF')
    source = p.inputs['Base Color'].links[0].from_socket
    mix = n.new('ShaderNodeMixRGB')
    mix.blend_type = 'MULTIPLY' if multiply else 'MIX'
    mix.inputs[0].default_value = factor
    mix.inputs[2].default_value = (*color, 1)
    l.new(source, mix.inputs[1])
    l.new(mix.outputs[0], p.inputs['Base Color'])
    if roughness is not None:
        for link in list(p.inputs['Roughness'].links):
            l.remove(link)
        p.inputs['Roughness'].default_value = roughness
    return material


def palette():
    return {
        'stone': tint(scanned('Ivory limestone | scanned grain', 'marble_01', .32, .85), (1,.95,.8)),
        'plaster': tint(scanned('Pale mineral plaster', 'plastered_wall_02', .45), (.81,.85,.79), .3, False),
        'jade': tint(scanned('Sea green marble | honed', 'marble_01', .38), (.19,.48,.39), roughness=.28),
        'darkjade': tint(scanned('Deep serpentine | polished', 'marble_01', .27), (.045,.135,.095), roughness=.21),
        'rose': tint(scanned('Rose sandstone', 'concrete_floor_02', .45), (.65,.29,.17), .68, False),
        'floor': tint(scanned('Weathered travertine paving', 'concrete_floor_02', .35), (.62,.57,.44), .65, False),
        'bronze': basic('Aged brass', (.3,.17,.058), .24, .9),
        'dark': basic('Oxidized bronze', (.03,.042,.037), .33, .78),
        'grout': basic('Lime mortar in recessed joints', (.23,.235,.205), .89),
        'copper': patina(),
    }


def patina():
    m = basic('Weathered copper | mineral patina', (.16,.38,.31), .38, .65)
    n,l=m.node_tree.nodes,m.node_tree.links
    p=n.get('Principled BSDF')
    tex=n.new('ShaderNodeTexNoise'); tex.inputs['Scale'].default_value=7; tex.inputs['Detail'].default_value=5
    coord=n.new('ShaderNodeTexCoord'); l.new(coord.outputs['Object'],tex.inputs['Vector'])
    ramp=n.new('ShaderNodeValToRGB')
    ramp.color_ramp.elements[0].position=.3; ramp.color_ramp.elements[0].color=(.025,.095,.065,1)
    ramp.color_ramp.elements[1].position=.72; ramp.color_ramp.elements[1].color=(.21,.42,.32,1)
    e=ramp.color_ramp.elements.new(.57); e.color=(.075,.25,.19,1)
    e=ramp.color_ramp.elements.new(.79); e.color=(.3,.135,.052,1)
    l.new(tex.outputs['Fac'],ramp.inputs[0]); l.new(ramp.outputs[0],p.inputs['Base Color'])
    bump=n.new('ShaderNodeBump'); bump.inputs['Strength'].default_value=.24; bump.inputs['Distance'].default_value=.015
    l.new(tex.outputs['Fac'],bump.inputs['Height']); l.new(bump.outputs[0],p.inputs['Normal'])
    return m


def curve(name, points, radius, material, cyclic=False):
    data=bpy.data.curves.new(name,'CURVE'); data.dimensions='3D'
    data.resolution_u=2; data.bevel_depth=radius; data.bevel_resolution=2
    spline=data.splines.new('POLY'); spline.points.add(len(points)-1)
    for p,co in zip(spline.points,points):p.co=(*co,1)
    spline.use_cyclic_u=cyclic
    o=bpy.data.objects.new(name,data); scene.collection.objects.link(o)
    data.materials.append(material)
    return o


def banded_pier(name, x, y, bottom, top, width, material, trim, joints=None):
    o=box(name,(x,y,(top+bottom)/2),(width,width,top-bottom),material,.018)
    box(name+' footing',(x,y,bottom+.1),(width+.18,width+.18,.2),trim,.024)
    box(name+' capital',(x,y,top-.06),(width+.16,width+.16,.12),trim,.012)
    if joints:
        for j in range(1,int((top-bottom)/.66)):
            z=bottom+j*.66
            box('Fine horizontal masonry joint',(x,y,z),(width+.002,width+.002,.009),joints,.001)
    return o


def arch(name, center, span, depth, spring, top, mat, rotate=0, base=0, trim=None):
    """An extruded wall with a genuine open semicircular arch, measured in meters."""
    cx,cy=center; r=span/2; pier=max(.18,span*.12)
    def tr(x,y,z):return (cx+x*math.cos(rotate)-y*math.sin(rotate),cy+x*math.sin(rotate)+y*math.cos(rotate),z)
    verts=[]; faces=[]; steps=48
    for j in range(steps+1):
        t=math.pi-j*math.pi/steps; x=r*math.cos(t); z=spring+r*math.sin(t)
        verts.extend([tr(x,-depth/2,z),tr(x,depth/2,z),tr(x,-depth/2,top),tr(x,depth/2,top)])
    for j in range(steps):
        a,b=4*j,4*j+4
        faces.extend([(a,b,b+1,a+1),(a+2,a+3,b+3,b+2),(a,a+2,b+2,b),(a+1,b+1,b+3,a+3)])
    faces.extend([(0,1,3,2),(4*steps,4*steps+2,4*steps+3,4*steps+1)])
    o=mesh(name+' arch',verts,faces,mat,.012)
    for x in (-r-pier/2,r+pier/2):
        p=box(name+' jamb',tr(x,0,(base+top)/2),(pier,depth,top-base),mat,.016)
        p.rotation_euler.z=rotate
    if trim:
        # Individually shaped arch stones with small real mortar gaps.
        for j in range(17):
            a=j*math.pi/17+.007; b=(j+1)*math.pi/17-.007
            vv=[]
            for y in (-depth/2-.026,depth/2+.026):
                for rr,t in ((r,a),(r,b),(r+.16,b),(r+.16,a)):
                    vv.append(tr(rr*math.cos(t),y,spring+rr*math.sin(t)))
            mesh(name+' voussoir',vv,CUBE_FACES,trim,.004)
    return o


def dome(name, center, radius, height, material, seam):
    x,y,z=center
    # Rounded onion profile, modeled as a smooth lathed metal shell.
    profile=[(0, .79),(.06,.91),(.18,1),(.34,.98),(.49,.85),(.63,.66),(.75,.45),(.86,.23),(.94,.09),(1,0.018)]
    # Catmull-Rom interpolation along the profile avoids visible rings.
    rings=[]
    for k in range(len(profile)-1):
        p0=Vector(profile[max(0,k-1)]); p1=Vector(profile[k]); p2=Vector(profile[k+1]); p3=Vector(profile[min(len(profile)-1,k+2)])
        for j in range(8):
            t=j/8
            v=.5*((2*p1)+(-p0+p2)*t+(2*p0-5*p1+4*p2-p3)*t*t+(-p0+3*p1-3*p2+p3)*t*t*t)
            rings.append((v.x,v.y))
    rings.append(profile[-1]); verts=[]; faces=[]; segments=96
    for zz,rr in rings:
        for k in range(segments):
            t=2*math.pi*k/segments
            verts.append((x+radius*rr*math.cos(t),y+radius*rr*math.sin(t),z+height*zz))
    for j in range(len(rings)-1):
        for k in range(segments):
            a=j*segments+k; b=j*segments+(k+1)%segments
            faces.append((a,b,b+segments,a+segments))
    o=mesh(name,verts,faces,material)
    for p in o.data.polygons:p.use_smooth=True
    for k in range(16):
        t=k*math.tau/16
        curve('Raised standing seam',[(x+radius*(rr+.003)*math.cos(t),y+radius*(rr+.003)*math.sin(t),z+height*zz) for zz,rr in rings],.006,seam)
    for rr,zz in ((.8,0),(.86,.03)):
        curve('Dome rolled rim',[(x+radius*rr*math.cos(t*math.tau/96),y+radius*rr*math.sin(t*math.tau/96),z+height*zz) for t in range(96)],.027,seam,True)
    rod('Gilded finial',(x,y,z+height*.96),(x,y,z+height+.42),.026,seam)
    bpy.ops.mesh.primitive_uv_sphere_add(segments=24,ring_count=12,radius=.075,location=(x,y,z+height+.18))
    bpy.context.object.data.materials.append(seam)
    for p in bpy.context.object.data.polygons:p.use_smooth=True


def tile_square(center, size, base, inlay, accent):
    x,y,z=center
    box('Inset stone paving',(x,y,z-.025),(size,size,.05),base,.006)
    for offset,width in ((.08,.017),(.15,.013)):
        w=size-2*offset
        for side in (-1,1):
            box('Bronze inlay border',(x+side*w/2,y,z+.002),(width,w,.005),inlay,.001)
            box('Bronze inlay border',(x,y+side*w/2,z+.002),(w,width,.005),inlay,.001)
    o=box('Diamond inlaid stone',(x,y,z+.003),(size*.25,size*.25,.009),accent,.002)
    o.rotation_euler.z=math.pi/4


def pavilion(name, center, width, height, P, lamp=False):
    x,y,z=center
    box(name+' stylobate',(x,y,z-.13),(width+.3,width+.3,.26),P['stone'],.02)
    tile_square((x,y,z+.006),width-.12,P['jade'],P['bronze'],P['stone'])
    top=z+height
    # Four open facades, with genuine arches and stone column bases.
    col=.13*width; span=width-col*2
    for cx,cy,rot in ((x,y-width/2+col/2,0),(x,y+width/2-col/2,0),(x-width/2+col/2,y,math.pi/2),(x+width/2-col/2,y,math.pi/2)):
        arch(name,(cx,cy),span,col,top-span/2-.15,top,P['stone'],rot,z)
    box(name+' cornice',(x,y,top+.04),(width+.22,width+.22,.16),P['stone'])
    box(name+' bronze roof curb',(x,y,top+.15),(width+.27,width+.27,.065),P['bronze'])
    dome(name+' copper dome',(x,y,top+.18),width*.7,width*.78,P['copper'],P['bronze'])
    if lamp:
        area(name+' warm interior',(x,y,top-.16),(x,y,z),75,(1,.59,.26),width*.55)


def stairs(a,b,width,mat,trim,rail=False,thickness=.3,step_count=None):
    a,b=Vector(a),Vector(b); planar=b-a; planar.z=0
    length=planar.length; direction=planar.normalized(); lateral=Vector((-direction.y,direction.x,0))
    count=step_count or max(2,round(abs(b.z-a.z)/.15))
    run=length/count; rise=(b.z-a.z)/count
    objs=[]
    verts=[tuple(p+lat*lateral+Vector((0,0,-thick))) for thick in (.12,thickness+.12) for p,lat in ((a,-width/2),(a,width/2),(b,width/2),(b,-width/2))]
    objs.append(mesh('Stair vault',verts,CUBE_FACES,mat,.009))
    for j in range(count):
        p=a+direction*((j+.5)*run); p.z=a.z+(j+1)*rise-.08
        o=box('Dressed stone tread',p,(run+.006,width,.16),mat,.009); o.rotation_euler.z=math.atan2(direction.y,direction.x); objs.append(o)
        p=a+direction*((j+.05)*run); p.z=a.z+(j+1)*rise+.003
        o=box('Brass step nosing',p,(.012,width-.12,.006),trim,.001); o.rotation_euler.z=math.atan2(direction.y,direction.x); objs.append(o)
    if rail:
        for side in (-1,1):
            aa=a+lateral*side*(width/2-.08)+Vector((0,0,.87)); bb=b+lateral*side*(width/2-.08)+Vector((0,0,.87))
            objs.append(rod('Slim brass handrail',aa,bb,.015,trim))
            for j in range(0,count,3):
                p=a+direction*((j+.5)*run)+lateral*side*(width/2-.08); p.z=a.z+(j+1)*rise
                objs.append(rod('Bronze baluster',p,aa.lerp(bb,(j+.5)/count),.011,trim))
    STAIR_FLIGHTS.append({'start':a.copy(),'end':b.copy(),'width':width,'objects':objs})
    return objs


def sightline_cut(sources, targets, direction=DIRECTION):
    """Boolean the projected source silhouettes out of foreground targets."""
    bpy.context.view_layer.update()
    right=Vector((-direction.y,direction.x,0)).normalized(); up=direction.cross(right).normalized()
    for source in sources:
        pts=[Vector(((source.matrix_world@v.co).dot(right),(source.matrix_world@v.co).dot(up))) for v in source.data.vertices]
        hull=convex_hull_2d(pts); ring=[pts[j] for j in hull]
        if len(ring)<3:continue
        verts=[tuple(right*v.x+up*v.y+direction*t) for t in (-100,100) for v in ring]; n=len(ring)
        faces=[tuple(reversed(range(n))),tuple(range(n,n*2))]+[(j,(j+1)%n,(j+1)%n+n,j+n) for j in range(n)]
        cutter=mesh('Sightline cutter',verts,faces,None)
        for obj in targets:
            if obj.type!='MESH':continue
            pp=[Vector(((obj.matrix_world@v.co).dot(right),(obj.matrix_world@v.co).dot(up))) for v in obj.data.vertices]
            if not pp or any(max(v[k] for v in pp)<min(v[k] for v in ring) or min(v[k] for v in pp)>max(v[k] for v in ring) for k in (0,1)):continue
            bpy.context.view_layer.objects.active=obj
            mod=obj.modifiers.new('View-dependent hidden cut','BOOLEAN'); mod.operation='DIFFERENCE'; mod.solver='EXACT'; mod.object=cutter
            bpy.ops.object.modifier_apply(modifier=mod.name)
        bpy.data.objects.remove(cutter,do_unlink=True)


def impossible_stairs(start, P, scale=1, base=0, rail=True, gates=None):
    width=1.35*scale; run=.65*scale; rise=.13*scale
    counts=(14,7,7,14); dirs=[Vector(v) for v in ((1,0,0),(0,1,0),(-1,0,0),(0,-1,0))]
    landings=[Vector(start)]; first=[]; last=[]
    for i,(count,d) in enumerate(zip(counts,dirs)):
        p=landings[-1]; q=p+d*(count*run+width)+Vector((0,0,count*rise))
        objs=stairs(p+d*width/2,q-d*width/2,width,P['stone'],P['bronze'],rail,step_count=count)
        if i==0:first=objs[:7]+[o for o in objs if 'handrail' in o.name]
        if i==3:last+=objs
        landings.append(q)
    if rail:
        for i,(p,q,d) in enumerate(zip(landings,landings[1:],dirs)):
            lateral=Vector((-d.y,d.x,0)); next_d=dirs[(i+1)%4]
            next_lat=Vector((-next_d.y,next_d.x,0))
            gate=(gates or {}).get((i+1)%4)
            def corner_segment(a,b):
                # A landing handrail follows its perimeter through one elbow.
                # Clip an actual entry opening where a pavilion branches off.
                intervals=[(0.,1.)]
                if gate:
                    normal=Vector((*gate,0)); tangent=Vector((-normal.y,normal.x,0))
                    relative=a-q; delta=b-a
                    enter,leave=0.,1.
                    for axis,lo,hi in ((normal,width/2-.22,width/2+.25),(tangent,-.44,.44)):
                        origin=relative.dot(axis); velocity=delta.dot(axis)
                        if abs(velocity)<1e-8:
                            if not lo<=origin<=hi:enter,leave=1.,0.;break
                        else:
                            aa,bb=sorted(((lo-origin)/velocity,(hi-origin)/velocity))
                            enter=max(enter,aa);leave=min(leave,bb)
                    if enter<leave:
                        intervals=[(0,enter),(leave,1)]
                parts=[]
                for lo,hi in intervals:
                    aa,bb=a.lerp(b,lo),a.lerp(b,hi)
                    if (bb-aa).length<.015:continue
                    parts.append(rod('Landing perimeter handrail',aa,bb,.015,P['bronze']))
                    for t,pt in ((lo,aa),(hi,bb)):
                        if .0001<t<.9999:parts.append(rod('Pavilion entry gatepost',pt-Vector((0,0,.87)),pt,.014,P['bronze']))
                return parts
            for side in (-1,1):
                offset=side*(width/2-.08); lift=Vector((0,0,.87))
                a=q-d*width/2+lateral*offset+lift
                elbow=q+(lateral+next_lat)*offset+lift
                c=q+next_d*width/2+next_lat*offset+lift
                assert (elbow-a).dot(d)>=-1e-6 and (c-elbow).dot(next_d)>=-1e-6
                rail_parts=corner_segment(a,elbow)+corner_segment(elbow,c)
                rail_parts.append(rod('Corner baluster',elbow-lift,elbow,.011,P['bronze']))
                if i==3:last.extend(rail_parts)
    for i,p in enumerate(landings):
        before=set(scene.objects)
        box('Illusion corner landing '+str(i),(p.x,p.y,p.z-.18),(width,width,.36),P['stone'])
        if i>0:
            banded_pier('Stair support '+str(i),p.x,p.y,base,p.z-.36,width*.77,P['plaster'],P['stone'],P['grout'])
        if i==4:last+=list(set(scene.objects)-before)
    sightline_cut(first,last)
    delta=landings[-1]-landings[0]
    assert (delta-DIRECTION*delta.dot(DIRECTION)).length<1e-5
    return landings


def clear_rock_paths(rocks):
    """Excavate clearance around stair flights instead of letting rocks penetrate them."""
    import bmesh
    bpy.context.view_layer.update()
    for flight in STAIR_FLIGHTS:
        a,b=flight['start'],flight['end']; direction=b-a; direction.z=0; direction.normalize()
        lateral=Vector((-direction.y,direction.x,0)); half=flight['width']/2+.14
        vv=[tuple(p+lateral*side+Vector((0,0,z))) for z in (-.52,2.25) for p,side in ((a,-half),(a,half),(b,half),(b,-half))]
        cutter=mesh('Excavated stair clearance',vv,CUBE_FACES,None)
        bm=bmesh.new(); bm.from_mesh(cutter.data); bmesh.ops.recalc_face_normals(bm,faces=bm.faces); bm.to_mesh(cutter.data); bm.free()
        lo=Vector([min(v[k] for v in vv) for k in range(3)]);hi=Vector([max(v[k] for v in vv) for k in range(3)])
        for rock in rocks:
            coords=[rock.matrix_world@Vector(v) for v in rock.bound_box]
            if any(max(v[k] for v in coords)<lo[k] or min(v[k] for v in coords)>hi[k] for k in range(3)):continue
            bpy.context.view_layer.objects.active=rock
            mod=rock.modifiers.new('Carved walking clearance','BOOLEAN'); mod.operation='DIFFERENCE'; mod.solver='EXACT'; mod.object=cutter
            bpy.ops.object.modifier_apply(modifier=mod.name)
        bpy.data.objects.remove(cutter,do_unlink=True)


def audit_stair_collisions(obstacles, label, objects=None):
    """Check evaluated surfaces, including bevels, for unintended path intersections."""
    from mathutils.bvhtree import BVHTree
    bpy.context.view_layer.update(); deps=bpy.context.evaluated_depsgraph_get(); cache={}
    def geometry(obj):
        if obj not in cache:
            evaluated=obj.evaluated_get(deps); data=evaluated.to_mesh()
            coords=[obj.matrix_world@v.co for v in data.vertices]
            if not coords:cache[obj]=None
            else:
                lo=[min(p[k] for p in coords) for k in range(3)]; hi=[max(p[k] for p in coords) for k in range(3)]
                cache[obj]=(lo,hi,BVHTree.FromPolygons(coords,[tuple(p.vertices) for p in data.polygons]))
            evaluated.to_mesh_clear()
        return cache[obj]
    collisions=[]
    groups=STAIR_FLIGHTS if objects is None else [{'objects':objects}]
    for f in groups:
        for part in f['objects']:
            if part.type!='MESH' or part.hide_render:continue
            aa=geometry(part)
            if aa is None:continue
            for obj in obstacles:
                if obj.type!='MESH' or obj.hide_render:continue
                bb=geometry(obj)
                if bb is None or any(aa[1][k]<bb[0][k] or aa[0][k]>bb[1][k] for k in range(3)):continue
                if aa[2].overlap(bb[2]):collisions.append((part.name,obj.name))
    print('COLLISION AUDIT',label,json.dumps(collisions))
    COLLISION_AUDITS.append({'check':label,'intersections':collisions})
    return collisions


def sea(size=160,z=-.1,deep=4,color=(.97,.99,1),wave=.06):
    water=basic('Sea water | dielectric 1.333',color,.027)
    p=water.node_tree.nodes.get('Principled BSDF'); p.inputs['Transmission Weight'].default_value=1; p.inputs['IOR'].default_value=1.333
    n,l=water.node_tree.nodes,water.node_tree.links
    coord=n.new('ShaderNodeTexCoord'); noise_tex=n.new('ShaderNodeTexNoise'); noise_tex.inputs['Scale'].default_value=3.8; noise_tex.inputs['Detail'].default_value=4; noise_tex.inputs['Roughness'].default_value=.65
    l.new(coord.outputs['Object'],noise_tex.inputs['Vector'])
    bump=n.new('ShaderNodeBump'); bump.inputs['Strength'].default_value=.45; bump.inputs['Distance'].default_value=.075
    l.new(noise_tex.outputs['Fac'],bump.inputs['Height']); l.new(bump.outputs[0],p.inputs['Normal'])
    absorb=n.new('ShaderNodeVolumeAbsorption'); absorb.inputs['Color'].default_value=(.16,.66,.77,1); absorb.inputs['Density'].default_value=.085
    l.new(absorb.outputs[0],n.get('Material Output').inputs['Volume'])
    N=240; verts=[]; faces=[]
    for j in range(N+1):
        y=size*(j/N-.5)
        for i in range(N+1):
            x=size*(i/N-.5)
            h=wave*(.58*math.sin(x*1.7+y*.55)+.28*math.sin(-x*.52+y*2.8)+.3*math.sin(x*.45+y*.8))
            verts.append((x,y,z+h))
    for j in range(N):
        for i in range(N):
            a=j*(N+1)+i; faces.append((a,a+1,a+N+2,a+N+1))
    boundary=list(range(N+1))+[j*(N+1)+N for j in range(1,N+1)]+[N*(N+1)+i for i in range(N-1,-1,-1)]+[j*(N+1) for j in range(N-1,0,-1)]
    bottom=[]
    for a in boundary:bottom.append(len(verts)); verts.append((verts[a][0],verts[a][1],-deep))
    for i in range(len(boundary)):
        k=(i+1)%len(boundary); faces.append((boundary[k],boundary[i],bottom[i],bottom[k]))
    faces.append(tuple(reversed(bottom)))
    o=mesh('Refracting sea | displaced surface and enclosed volume',verts,faces,water)
    for p in o.data.polygons:p.use_smooth=True
    sand=tint(scanned('Submerged limestone sand','concrete_floor_02',.14),(.57,.66,.65),.8,False)
    box('Seabed',(0,0,-deep-.12),(size,size,.2),sand,0)
    return o


def rock_material():
    m=scanned('Eroded rose sandstone | grain and strata','concrete_floor_02',1.4,.95)
    n,l=m.node_tree.nodes,m.node_tree.links; p=n.get('Principled BSDF')
    tex=n.new('ShaderNodeTexNoise'); tex.inputs['Scale'].default_value=.72; tex.inputs['Detail'].default_value=5; tex.inputs['Roughness'].default_value=.72
    coord=n.new('ShaderNodeTexCoord'); l.new(coord.outputs['Object'],tex.inputs['Vector'])
    ramp=n.new('ShaderNodeValToRGB'); ramp.color_ramp.elements[0].position=.2; ramp.color_ramp.elements[0].color=(.19,.075,.037,1); ramp.color_ramp.elements[1].position=.78; ramp.color_ramp.elements[1].color=(.68,.34,.18,1)
    e=ramp.color_ramp.elements.new(.48); e.color=(.42,.17,.082,1)
    l.new(tex.outputs['Fac'],ramp.inputs[0]); l.new(ramp.outputs[0],p.inputs['Base Color'])
    wave=n.new('ShaderNodeTexWave'); wave.wave_type='BANDS'; wave.bands_direction='Z'; wave.inputs['Scale'].default_value=5; wave.inputs['Distortion'].default_value=5; wave.inputs['Detail Scale'].default_value=.5
    l.new(coord.outputs['Object'],wave.inputs['Vector'])
    bump=n.new('ShaderNodeBump'); bump.inputs['Strength'].default_value=.18; bump.inputs['Distance'].default_value=.009
    l.new(wave.outputs[0],bump.inputs['Height'])
    old=p.inputs['Normal'].links[0].from_socket; l.new(old,bump.inputs['Normal']); l.new(bump.outputs[0],p.inputs['Normal'])
    return m


def rock(name,location,dimensions,material,seed=1):
    rng=random.Random(seed)
    bpy.ops.mesh.primitive_ico_sphere_add(subdivisions=5,radius=1,location=location)
    o=bpy.context.object; o.name=name
    shift=Vector((rng.random()*40,rng.random()*40,rng.random()*40))
    for v in o.data.vertices:
        p=v.co.copy()
        large=noise.noise_vector(p*2.3+shift)
        fine=noise.fractal(p*12+shift,.9,2,3)
        p*=1+.25*large.x+.05*fine
        # Sandstone fracture planes; soften only at the grain scale.
        p.x=max(-.79,min(.85,p.x)); p.y=max(-.81,min(.88,p.y))
        v.co=Vector((p.x*dimensions[0]/2,p.y*dimensions[1]/2,p.z*dimensions[2]/2))
    o.data.materials.append(material)
    for p in o.data.polygons:p.use_smooth=True
    return o


_rock_parts=None
def scanned_rock(name,location,dimensions,seed=0):
    global _rock_parts
    if _rock_parts is None:
        before=set(scene.objects)
        bpy.ops.import_scene.gltf(filepath=str(ROOT/'assets/namaqualand_rocks_01/namaqualand_rocks_01_2k.gltf'))
        _rock_parts=sorted([o for o in set(scene.objects)-before if o.type=='MESH'],key=lambda o:o.name)
        bpy.context.view_layer.update()
        for obj in _rock_parts:
            matrix=obj.matrix_world.copy(); obj.parent=None; obj.matrix_world.identity()
            coords=[matrix@v.co for v in obj.data.vertices]
            lo=Vector([min(p[k] for p in coords) for k in range(3)]); hi=Vector([max(p[k] for p in coords) for k in range(3)])
            mid=(lo+hi)/2; span=hi-lo
            for v,p in zip(obj.data.vertices,coords):v.co=Vector([(p[k]-mid[k])/span[k] for k in range(3)])
            obj.hide_render=True; obj.hide_viewport=True
        material=_rock_parts[0].data.materials[0]
        tint(material,(1,.81,.68))
    # The pale quartz and ochre variants complement the reference's warm island.
    prototype=_rock_parts[(0,3,0,1)[seed%4]]
    obj=prototype.copy(); obj.data=prototype.data.copy(); scene.collection.objects.link(obj)
    obj.name=name; obj.hide_render=False; obj.hide_viewport=False
    angle=(seed%4)*math.pi/2
    rotated=[Vector((v.co.x*math.cos(angle)-v.co.y*math.sin(angle),v.co.x*math.sin(angle)+v.co.y*math.cos(angle),v.co.z)) for v in obj.data.vertices]
    lo=Vector([min(p[k] for p in rotated) for k in range(3)]); hi=Vector([max(p[k] for p in rotated) for k in range(3)])
    for vert,p in zip(obj.data.vertices,rotated):vert.co=Vector([((p[k]-(lo[k]+hi[k])/2)/(hi[k]-lo[k]))*dimensions[k] for k in range(3)])
    obj.location=location
    return obj


def shoreline(rocks,center,z=-.1,wave=.095):
    """Trace the modeled island's waterline; add a broken, translucent foam fringe."""
    from mathutils.bvhtree import BVHTree
    bpy.context.view_layer.update(); deps=bpy.context.evaluated_depsgraph_get()
    bvhs=[]
    for obj in rocks:
        points=[obj.matrix_world@v.co for v in obj.data.vertices]
        bvhs.append(BVHTree.FromPolygons(points,[tuple(p.vertices) for p in obj.data.polygons]))
    x,y=center
    def land(xx,yy):
        for tree in bvhs:
            hit=tree.ray_cast(Vector((xx,yy,30)),Vector((0,0,-1)),35)
            if hit[0] is not None and hit[0].z>z:return True
        return False
    verts=[]; faces=[]; N=480; M=7
    for j in range(N):
        t=j*math.tau/N; u,v=math.cos(t),math.sin(t)
        # Outermost submerged-to-dry transition, even with gaps between boulders.
        r=12
        while r>.1 and not land(x+r*u,y+r*v):r-=.13
        lo,hi=r,r+.13
        for _ in range(5):
            mid=(lo+hi)/2
            if land(x+mid*u,y+mid*v):lo=mid
            else:hi=mid
        radius=(lo+hi)/2
        for i in range(M):
            rr=radius-.055+i/(M-1)*(.4+.13*math.sin(t*19))
            xx,yy=x+u*rr,y+v*rr
            h=wave*(.58*math.sin(xx*1.7+yy*.55)+.28*math.sin(-xx*.52+yy*2.8)+.3*math.sin(xx*.45+yy*.8))
            verts.append((xx,yy,z+h+.025))
    for j in range(N):
        for i in range(M-1):
            a=j*M+i; b=((j+1)%N)*M+i; faces.append((a,b,b+1,a+1))
    mat=basic('Broken sea foam',(.8,.9,.89),.48)
    n,l=mat.node_tree.nodes,mat.node_tree.links
    coord=n.new('ShaderNodeTexCoord'); tex=n.new('ShaderNodeTexNoise'); tex.inputs['Scale'].default_value=12; tex.inputs['Detail'].default_value=3
    l.new(coord.outputs['Object'],tex.inputs['Vector'])
    ramp=n.new('ShaderNodeValToRGB'); ramp.color_ramp.elements[0].position=.48; ramp.color_ramp.elements[1].position=.65
    l.new(tex.outputs['Fac'],ramp.inputs[0])
    transp=n.new('ShaderNodeBsdfTransparent'); mix=n.new('ShaderNodeMixShader')
    l.new(ramp.outputs[0],mix.inputs[0]); l.new(transp.outputs[0],mix.inputs[1]); l.new(n.get('Principled BSDF').outputs[0],mix.inputs[2]); l.new(mix.outputs[0],n.get('Material Output').inputs['Surface'])
    foam=mesh('Sea foam following the actual rock waterline',verts,faces,mat)
    for p in foam.data.polygons:p.use_smooth=True


_plant_parts=None
def plant(location,height=1.6,rotation=0):
    global _plant_parts
    if _plant_parts is None:
        before=set(scene.objects)
        bpy.ops.import_scene.gltf(filepath=str(ROOT/'assets/potted_plant_01/potted_plant_01_2k.gltf'))
        parts=[o for o in set(scene.objects)-before if o.type=='MESH']; bpy.context.view_layer.update()
        coords=[o.matrix_world@Vector(v) for o in parts for v in o.bound_box]
        low=min(v.z for v in coords); high=max(v.z for v in coords)
        cx=(min(v.x for v in coords)+max(v.x for v in coords))/2; cy=(min(v.y for v in coords)+max(v.y for v in coords))/2
        for o in parts:
            matrix=o.matrix_world.copy(); o.parent=None; o.matrix_world.identity()
            for v in o.data.vertices:v.co=(matrix@v.co-Vector((cx,cy,low)))/(high-low)
            o.hide_render=True; o.hide_viewport=True
        _plant_parts=parts
    for obj in _plant_parts:
        o=obj.copy(); scene.collection.objects.link(o); o.hide_render=False; o.hide_viewport=False
        o.location=location; o.scale=(height,)*3; o.rotation_euler.z=rotation


def sky(elevation=32,rotation=215,strength=.45,exposure=-1):
    world=bpy.data.worlds.new('Physical atmosphere'); world.use_nodes=True; scene.world=world
    n,l=world.node_tree.nodes,world.node_tree.links
    t=n.new('ShaderNodeTexSky'); t.sky_type='NISHITA'; t.sun_elevation=math.radians(elevation); t.sun_rotation=math.radians(rotation); t.sun_size=math.radians(.9); t.air_density=1.1; t.dust_density=1.4
    l.new(t.outputs[0],n.get('Background').inputs['Color']); n.get('Background').inputs['Strength'].default_value=strength
    scene.view_settings.exposure=exposure


def night():
    world=bpy.data.worlds.new('Blue hour atmosphere'); world.use_nodes=True; scene.world=world
    bg=world.node_tree.nodes.get('Background'); bg.inputs['Color'].default_value=(.17,.23,.42,1); bg.inputs['Strength'].default_value=.24
    scene.view_settings.exposure=.7
    area('Cool moon key',(-10,-4,24),(0,0,6),5200,(.57,.72,1),8)
    area('Soft warm horizon',(10,12,15),(0,0,7),4200,(1,.64,.34),7)
    area('Broad sky reflection',(4,-12,18),(0,0,5),1800,(.55,.81,1),11)


def camera(target,scale,direction=DIRECTION):
    bpy.ops.object.camera_add(); o=bpy.context.object; o.name='ORTHOGRAPHIC | fixed illusion viewpoint'
    o.location=Vector(target)+direction*65; o.rotation_euler=(Vector(target)-o.location).to_track_quat('-Z','Y').to_euler()
    o.data.type='ORTHO'; o.data.ortho_scale=scale; o.data.clip_end=400; scene.camera=o
    return o


def render(tag,preview,reference,alignments=(),reveal=False):
    out=ROOT/'output/monuments'; out.mkdir(parents=True,exist_ok=True)
    path=out/'previews' if preview else out; path.mkdir(exist_ok=True)
    if reveal:
        target=scene.camera.location-DIRECTION*65
        d=(DIRECTION+Vector((.35,.25,0))).normalized()
        scene.camera.location=target+d*65
        scene.camera.rotation_euler=(target-scene.camera.location).to_track_quat('-Z','Y').to_euler()
        tag+='-reveal'
    from bpy_extras.object_utils import world_to_camera_view
    bpy.context.view_layer.update(); errors=[]
    for a,b in alignments:
        aa=world_to_camera_view(scene,scene.camera,Vector(a)); bb=world_to_camera_view(scene,scene.camera,Vector(b))
        error=math.hypot((aa.x-bb.x)*scene.render.resolution_x,(aa.y-bb.y)*scene.render.resolution_y); errors.append(error)
        if not reveal:assert error<.01,error
    scene.render.filepath=str(path/(tag+'.png'))
    scene['collision_audits']=json.dumps(COLLISION_AUDITS)
    if not preview:
        bpy.ops.file.pack_all(); bpy.ops.wm.save_as_mainfile(filepath=str(out/(tag+'.blend')))
    bpy.ops.render.render(write_still=True)
    if not preview:
        scene.render.image_settings.file_format='OPEN_EXR'; scene.render.image_settings.color_depth='32'
        bpy.data.images['Render Result'].save_render(str(out/(tag+'.exr')),scene=scene)
        info={'renderer':'Blender '+bpy.app.version_string+' / Cycles','camera_type':scene.camera.data.type,'orthographic_scale':scene.camera.data.ortho_scale,'resolution':[scene.render.resolution_x,scene.render.resolution_y],'max_samples':scene.cycles.samples,'denoised':True,'png_bit_depth':16,'exr_bit_depth':32,'reference':reference,'alignment_error_pixels':errors,'image_generation':False,'composited':False,'perspective_geometry_correction':False,'textures_packed':all(i.packed_file for i in bpy.data.images if i.source=='FILE')}
        info['collision_audits']=COLLISION_AUDITS
        (out/(tag+'-info.json')).write_text(json.dumps(info,indent=2)+'\n')
    print('FINISHED',tag, 'alignment errors:',errors)
