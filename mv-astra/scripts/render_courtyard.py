"""Build and path trace a camera-aligned Penrose staircase in Blender Cycles.

blender -b --python scripts/render_courtyard.py -- --preview
blender -b --python scripts/render_courtyard.py -- --variant daylight
blender -b --python scripts/render_courtyard.py -- --projection orthographic
All geometry, materials, illumination and camera settings live in this file.
The apparent closing corner is a forced-perspective overlap of two landings.
"""
import argparse
import json
import math
import random
import sys
from pathlib import Path

import bpy
from mathutils import Vector
from mathutils.geometry import convex_hull_2d

ROOT = Path(__file__).resolve().parents[1]
OUT = ROOT / 'output' / 'cycles'
OUT.mkdir(parents=True, exist_ok=True)
parser = argparse.ArgumentParser()
parser.add_argument('--preview', action='store_true')
parser.add_argument('--variant', choices=['daylight', 'evening'], default='daylight')
parser.add_argument('--projection', choices=['perspective', 'orthographic'], default='perspective')
parser.add_argument('--geometry-only', action='store_true')
parser.add_argument('--reveal', action='store_true')
parser.add_argument('--samples', type=int, default=512)
args = parser.parse_args(sys.argv[sys.argv.index('--') + 1:] if '--' in sys.argv else [])
random.seed(17)
bpy.ops.object.select_all(action='SELECT')
bpy.ops.object.delete(use_global=False)
scene = bpy.context.scene
scene.render.engine = 'CYCLES'
scene.cycles.samples = 48 if args.preview else args.samples
scene.cycles.use_denoising = True
scene.cycles.adaptive_threshold = .03 if args.preview else .008
scene.cycles.max_bounces = 12
scene.cycles.diffuse_bounces = 6
scene.cycles.glossy_bounces = 6
scene.cycles.transmission_bounces = 8
scene.cycles.seed = 23
try:
    prefs = bpy.context.preferences.addons['cycles'].preferences
    prefs.compute_device_type = 'METAL'
    prefs.get_devices()
    gpu = False
    for device in prefs.devices:
        device.use = device.type == 'METAL'
        gpu |= device.use
        print('Render device:', device.name, device.type, device.use)
    scene.cycles.device = 'GPU' if gpu else 'CPU'
except Exception as exc:
    print('Using CPU:', exc)
scene.render.resolution_x = 1050 if args.preview else 2400
scene.render.resolution_y = 900 if args.preview else 2056
scene.render.resolution_percentage = 100
scene.render.image_settings.file_format = 'PNG'
scene.render.image_settings.color_mode = 'RGB'
scene.render.image_settings.color_depth = '16'
scene.view_settings.view_transform = 'AgX'
scene.view_settings.look = 'AgX - Medium High Contrast'
scene.view_settings.exposure = -1.05
scene.unit_settings.system = 'METRIC'

def basic(name, color, roughness=.5, metallic=0):
    m = bpy.data.materials.new(name)
    m.use_nodes = True
    p = m.node_tree.nodes.get('Principled BSDF')
    p.inputs['Base Color'].default_value = (*color, 1)
    p.inputs['Roughness'].default_value = roughness
    p.inputs['Metallic'].default_value = metallic
    return m

manifest_path = ROOT / 'assets/textures/manifest.json'
manifest = json.loads(manifest_path.read_text()) if manifest_path.exists() else {}

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

stone = scanned('Honed marble | scanned stone', 'marble_01', .28, .8)
if args.variant=='evening':
    sn,sl=stone.node_tree.nodes,stone.node_tree.links
    sp=sn.get('Principled BSDF')
    source=sp.inputs['Base Color'].links[0].from_socket
    tint=sn.new('ShaderNodeMixRGB')
    tint.blend_type='MULTIPLY'
    tint.inputs[0].default_value=1
    tint.inputs[2].default_value=(.085,.245,.19,1)
    sl.new(source,tint.inputs[1])
    sl.new(tint.outputs[0],sp.inputs['Base Color'])
    for link in list(sp.inputs['Roughness'].links):sl.remove(link)
    sp.inputs['Roughness'].default_value=.19
plaster = scanned('Mineral lime plaster', 'plastered_wall_02', .34)
floor = scanned('Worn limestone floor', 'concrete_floor_02', .23, .75)
# Light, honed limestone retains scanned variation without a dirty concrete look.
fn,fl=floor.node_tree.nodes,floor.node_tree.links
fp=fn.get('Principled BSDF')
original=fp.inputs['Base Color'].links[0].from_socket
mix=fn.new('ShaderNodeMixRGB')
mix.blend_type='MIX'
mix.inputs[0].default_value=.64
mix.inputs[2].default_value=(.56,.52,.43,1)
fl.new(original,mix.inputs[1])
fl.new(mix.outputs[0],fp.inputs['Base Color'])
bronze = basic('Brushed aged bronze', (.23, .115, .045), .25, .86)
dark = basic('Dark bronze window frames', (.055, .047, .035), .36, .72)
grout = basic('Recessed stone joints', (.16, .145, .115), .8)

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

# Four genuinely ascending flights. Unequal lengths make the net displacement
# exactly parallel to the camera viewing direction, closing the loop in projection.
WIDTH = 1.5
RUN, RISE = .65, .13
counts = (14, 7, 7, 14)
directions = [Vector((1,0,0)), Vector((0,1,0)), Vector((-1,0,0)), Vector((0,-1,0))]
p = Vector((0, 0, 2.4))
landings = [p.copy()]
first_flight=[]
last_flight=[]
for flight,(count, direction) in enumerate(zip(counts, directions)):
    before_flight=set(scene.objects)
    q = p + direction * (count * RUN + WIDTH) + Vector((0,0,count*RISE))
    lateral = Vector((-direction.y, direction.x, 0))
    start = p + direction * (WIDTH/2)
    # Each run has a sloping continuous soffit and individually modelled treads.
    a = start - lateral * WIDTH/2
    b = start + lateral * WIDTH/2
    end = q - direction * WIDTH/2
    c, d = end + lateral*WIDTH/2, end-lateral*WIDTH/2
    upper = [a, b, c, d]
    verts = [tuple(v-Vector((0,0,.13))) for v in upper] + [tuple(v-Vector((0,0,.52))) for v in upper]
    soffit=mesh('Continuous stair soffit', verts, [(0,1,2,3),(4,7,6,5),(0,4,5,1),(1,5,6,2),(2,6,7,3),(3,7,4,0)], plaster, .009)
    if flight==0:first_flight.append(soffit)
    for j in range(count):
        center = start + direction*((j+.5)*RUN)
        center.z = p.z+(j+1)*RISE-.115
        dims = (RUN+.006, WIDTH, .23) if direction.x else (WIDTH,RUN+.006,.23)
        tread=box('Marble tread', center, dims, stone, .007)
        if flight==0 and j<3:first_flight.append(tread)
        # A thin inset bronze strip makes each rising edge readable.
        edge = start+direction*((j+.08)*RUN)
        edge.z = p.z+(j+1)*RISE+.001
        dims = (.012, WIDTH-.16, .003) if direction.x else (WIDTH-.16,.012,.003)
        box('Inlaid bronze nosing', edge, dims, bronze, .001)
    p = q
    landings.append(p.copy())
    if flight==3:last_flight=list(set(scene.objects)-before_flight)

# Fine real-metal guardrails and balusters provide familiar architectural scale.
for side in (-1,1):
    rail_radius=.019
    offset=side*(WIDTH/2-.095)
    for i,(p,q,direction,count) in enumerate(zip(landings,landings[1:],directions,counts)):
        before_rail=set(scene.objects)
        lateral=Vector((-direction.y,direction.x,0))
        a=p+direction*WIDTH/2+lateral*offset+Vector((0,0,.94))
        b=q-direction*WIDTH/2+lateral*offset+Vector((0,0,.94))
        handrail=rod('Bronze sloping handrail',a,b,rail_radius,bronze)
        if i==0:first_flight.append(handrail)
        for j in range(0,count,3):
            center=p+direction*(WIDTH/2+(j+.5)*RUN)+lateral*offset
            t=(j+.5)/count
            center.z=p.z+(j+1)*RISE
            top=a.lerp(b,t)
            rod('Slender bronze baluster',center,top,.013,bronze)
        p2=p+lateral*offset+Vector((0,0,.94))
        q2=q+lateral*offset+Vector((0,0,.94))
        handrail=rod('Landing handrail',p2,a,rail_radius,bronze)
        if i==0:first_flight.append(handrail)
        rod('Landing handrail',b,q2,rail_radius,bronze)
        nextdir=directions[(i+1)%4]
        nextlat=Vector((-nextdir.y,nextdir.x,0))
        elbow=q+(lateral+nextlat)*offset+Vector((0,0,.94))
        nextpoint=q+nextlat*offset+Vector((0,0,.94))
        rod('Bronze railing elbow',q2,elbow,rail_radius,bronze)
        rod('Bronze railing elbow',elbow,nextpoint,rail_radius,bronze)
        if i==3:last_flight.extend(set(scene.objects)-before_rail)

camera_dir = (landings[-1] - landings[0]).normalized()
closure = landings[-1] - landings[0]
residual = closure - camera_dir * closure.dot(camera_dir)
assert residual.length < 1e-5  # mathutils stores single-precision coordinates
print('Projection closure residual (m):', residual.length)
terminal=[]
for i,p in enumerate(landings):
    before=set(scene.objects)
    box('Corner landing '+str(i), (p.x,p.y,p.z-.21), (WIDTH,WIDTH,.42), stone, .009)
    if i>0:
        # Tall piers supply architectural scale and contact shadows.
        box('Landing pier '+str(i), (p.x,p.y,(p.z-.42)/2), (1.22,1.22,p.z-.42), plaster, .018)
        box('Pier foot '+str(i), (p.x,p.y,.1), (1.45,1.45,.2), stone)
        for z in [x*.62 for x in range(1,int((p.z-.5)/.62))]:
            box('Pier horizontal joint', (p.x,p.y,z), (1.224,1.224,.009), grout,.001)
    if i==4:terminal=list(set(scene.objects)-before)+last_flight

# Cut the foreground terminal along the projected silhouette of the beginning
# flight. The cuts run exactly along sight lines; the hidden depth gap is real.
# This lets the rising first treads appear in front of the closing landing.
bpy.context.view_layer.update()
right=Vector((camera_dir.y*-1,camera_dir.x,0)).normalized()
up=camera_dir.cross(right).normalized()
for source in first_flight:
    points=[source.matrix_world@v.co for v in source.data.vertices]
    pts=[Vector((v.dot(right),v.dot(up))) for v in points]
    hull=convex_hull_2d(pts)
    ring=[pts[j] for j in hull]
    verts=[tuple(right*v.x+up*v.y+camera_dir*t) for t in (-35,65) for v in ring]
    n=len(ring)
    faces=[tuple(reversed(range(n))),tuple(range(n,2*n))]
    faces.extend((j,(j+1)%n,(j+1)%n+n,j+n) for j in range(n))
    cutter=mesh('Camera-aligned construction cutter',verts,faces,None)
    for obj in terminal:
        projected=[Vector(((obj.matrix_world@v.co).dot(right),(obj.matrix_world@v.co).dot(up))) for v in obj.data.vertices]
        if not projected:continue
        if any(max(v[axis] for v in projected)<min(v[axis] for v in ring) or min(v[axis] for v in projected)>max(v[axis] for v in ring) for axis in (0,1)):continue
        bpy.context.view_layer.objects.active=obj
        mod=obj.modifiers.new('Hidden alignment cut','BOOLEAN')
        mod.operation='DIFFERENCE'
        mod.solver='EXACT'
        mod.object=cutter
        bpy.ops.object.modifier_apply(modifier=mod.name)
    bpy.data.objects.remove(cutter,do_unlink=True)

# Perspective mode converts the orthographic design for a perspective camera.
# Orthographic mode uses the original, unwarped stair geometry directly.
target=Vector((5.1,1.8,3.5))
camera_distance=45
if args.projection=='perspective':
    for obj in list(scene.objects):
        if obj.type!='MESH':continue
        matrix=obj.matrix_world.copy()
        inv=matrix.inverted()
        for vertex in obj.data.vertices:
            delta=matrix@vertex.co-target
            depth=delta.dot(camera_dir)
            transverse=delta-camera_dir*depth
            vertex.co=inv@(target+transverse*(camera_distance-depth)/camera_distance+camera_dir*depth)

if not args.geometry_only:
    # A continuous full-scale courtyard, never a floating diorama plinth.
    box('Courtyard foundation', (4,1,-1), (55,55,.4), grout)
    for ix in range(-9,16):
        for iy in range(-9,13):
            x,y = ix*1.5, iy*1.5
            # Long reflecting pool occupies the right-hand foreground.
            if 12.0 <= x <= 16.5 and -10.5 <= y <= 10.5: continue
            box('Limestone paving', (x,y,-.025), (1.492,1.492,.12), floor,.005)
    # Pool basin, tiled bottom and physical refracting water surface.
    pool_tile=basic('Muted celadon pool tiles',(.17,.33,.29),.27)
    box('Pool bed', (14.25,0,-.42), (5.99,23.99,.2), pool_tile)
    for x in (11.25,17.25):box('Pool side',(x,0,-.24),(.08,24,.5),stone)
    water = basic('Water | dielectric IOR 1.333', (.93,.985,.99), .025)
    pn = water.node_tree.nodes.get('Principled BSDF')
    pn.inputs['Transmission Weight'].default_value = 1
    pn.inputs['IOR'].default_value = 1.333
    n,l = water.node_tree.nodes, water.node_tree.links
    tex = n.new('ShaderNodeTexNoise')
    tex.inputs['Scale'].default_value = 5
    tex.inputs['Detail'].default_value = 3
    bump=n.new('ShaderNodeBump')
    bump.inputs['Strength'].default_value=.25
    bump.inputs['Distance'].default_value=.022
    coord=n.new('ShaderNodeTexCoord')
    l.new(coord.outputs['Object'],tex.inputs['Vector'])
    l.new(tex.outputs['Fac'],bump.inputs['Height'])
    l.new(bump.outputs['Normal'],pn.inputs['Normal'])
    box('Reflecting water', (14.25,0,-.16), (5.98,23.98,.25), water,0)

    def arcade(name, center, rotate=0):
        # A rectangular wall with a real semicircular arch opening.
        r,spring,height,depth=1.5,3.35,7.7,.75
        cx,cy=center
        def transform(x,y,z):
            return (cx+x*math.cos(rotate)-y*math.sin(rotate),cy+x*math.sin(rotate)+y*math.cos(rotate),z)
        verts,faces=[],[]
        steps=40
        for j in range(steps+1):
            theta=math.pi-j*math.pi/steps
            x=r*math.cos(theta)
            z=spring+r*math.sin(theta)
            verts.extend([transform(x,-depth/2,z),transform(x,depth/2,z),transform(x,-depth/2,height),transform(x,depth/2,height)])
        for j in range(steps):
            a,b=j*4,(j+1)*4
            faces.extend([(a,b,b+1,a+1),(a+2,a+3,b+3,b+2),(a,a+2,b+2,b),(a+1,b+1,b+3,a+3)])
        faces.extend([(0,1,3,2),(steps*4,steps*4+2,steps*4+3,steps*4+1)])
        mesh(name+' arch vault',verts,faces,plaster,.009)
        for x in (-1.87,1.87):
            loc=transform(x,0,height/2)
            obj=box(name+' pier',loc,(.74,depth,height),plaster)
            obj.rotation_euler.z=rotate
            loc=transform(x,0,.16)
            obj=box(name+' stone base',loc,(.87,.88,.32),stone)
            obj.rotation_euler.z=rotate
        obj=box(name+' cornice',transform(0,0,height-.13),(4.5,.92,.26),stone)
        obj.rotation_euler.z=rotate
    for x in (-4, .48, 4.96,9.44,13.92,18.4):
        arcade('North colonnade', (x,10.8))
    for y in (-8,-3.52,.96,5.44,9.92):
        arcade('West colonnade',(-5.9,y),math.pi/2)
    box('North inner wall',(6,14.3,4.2),(31,.5,8.4),plaster)
    box('West inner wall',(-9.4,1,4.2),(.5,32,8.4),plaster)
    box('North portico ceiling',(6,12.7,7.75),(31,4.7,.35),plaster)
    box('West portico ceiling',(-7.7,1,7.75),(4.6,32,.35),plaster)
    # Contemporary bronze-framed glass doors in the shaded north portico.
    glass=basic('Window glass',(.92,.96,.97),.09)
    glass.node_tree.nodes.get('Principled BSDF').inputs['Transmission Weight'].default_value=1
    for x in (-.5,4,8.5,13):
        box('Glass door',(x,14.01,1.9),(2.45,.055,3.8),glass,.001)
        for dx in (-1.24,0,1.24):box('Door bronze mullion',(x+dx,13.96,1.9),(.045,.07,3.8),dark,.003)
        for z in (.03,3.78):box('Door bronze transom',(x,13.96,z),(2.5,.07,.045),dark,.003)
    # Spare benches beneath the colonnade establish meter-scale detail.
    for x in (0,8.6):
        for y in (12.15,):
            box('Honed stone bench',(x,y,.56),(2.8,.65,.16),stone,.022)
            for dx in (-1,1):box('Bench pedestal',(x+dx,y,.27),(.17,.49,.52),dark,.012)

    plant_path=ROOT/'assets/potted_plant_01/potted_plant_01_2k.gltf'
    if plant_path.exists():
        before=set(scene.objects)
        bpy.ops.import_scene.gltf(filepath=str(plant_path))
        parts=[o for o in set(scene.objects)-before if o.type=='MESH']
        bpy.context.view_layer.update()
        coords=[o.matrix_world@Vector(v) for o in parts for v in o.bound_box]
        low=min(v.z for v in coords)
        high=max(v.z for v in coords)
        cx=(min(v.x for v in coords)+max(v.x for v in coords))/2
        cy=(min(v.y for v in coords)+max(v.y for v in coords))/2
        height=high-low
        print('Imported plant height:',height)
        # Bake import transforms once, then instance the photographed plant.
        for obj in parts:
            matrix=obj.matrix_world.copy()
            obj.parent=None
            obj.matrix_world.identity()
            for v in obj.data.vertices:
                v.co=(matrix@v.co-Vector((cx,cy,low)))*(2.45/height)
        locations=[(-3.5,-2.6,.04),(-3.5,5.8,.04),(3.2,12.1,.04),(12.1,12.1,.04)]
        for index,loc in enumerate(locations):
            for obj in parts:
                o=obj if index==0 else obj.copy()
                if index:scene.collection.objects.link(o)
                o.location=loc
                o.rotation_euler.z=index*1.9

# Continue the background beyond the crop, avoiding a visible diorama edge.
if not args.geometry_only:
    box('Distant ground',(0,0,-1.3),(300,300,.2),floor)

# Physical sky and direct sunlight. Evening adds actual lamps and warm bounce.
world=bpy.data.worlds.new('Physical sky')
world.use_nodes=True
scene.world=world
nodes=world.node_tree.nodes
sky=nodes.new('ShaderNodeTexSky')
sky.sky_type='NISHITA'
sky.sun_elevation=math.radians(30 if args.variant=='daylight' else 4)
sky.sun_rotation=math.radians(218)
sky.sun_size=math.radians(.8)
sky.air_density=1.1
sky.dust_density=1.5
bg=nodes.get('Background')
bg.inputs['Strength'].default_value=.45 if args.variant=='daylight' else .2
world.node_tree.links.new(sky.outputs['Color'],bg.inputs['Color'])
if args.variant=='evening':
    scene.view_settings.exposure=.2
    for x in (-4,.48,4.96,9.44,13.92):
        area('Warm portico uplight',(x,12,1.2),(x,10.5,5),160,(1,.57,.26),.4)
    area('Large warm courtyard fill',(0,-8,11),(5,1,3),2200,(1,.74,.5),7)

bpy.ops.object.camera_add()
camera=bpy.context.object
camera.name='Illusion camera | keep direction fixed'
if args.reveal: camera_dir=(camera_dir+Vector((.38,.28,0))).normalized()
camera.location=target+camera_dir*45
camera.rotation_euler=(target-camera.location).to_track_quat('-Z','Y').to_euler()
camera.data.type='ORTHO' if args.projection=='orthographic' else 'PERSP'
camera.data.sensor_width=36
framing_width=21.8 if not args.geometry_only else 17
camera.data.ortho_scale=framing_width
camera.data.lens=36*camera_distance/framing_width
scene.camera=camera
scene.render.film_transparent=False
projection_suffix='-orthographic' if args.projection=='orthographic' else ''
tag=args.variant+projection_suffix+('-reveal' if args.reveal else '')+('-geometry' if args.geometry_only else '')+('-preview' if args.preview else '')
print('Camera projection:',camera.data.type,'Perspective geometry correction:',args.projection=='perspective')
if args.projection=='orthographic' and not args.reveal:
    from bpy_extras.object_utils import world_to_camera_view
    bpy.context.view_layer.update()
    a=world_to_camera_view(scene,camera,landings[0])
    b=world_to_camera_view(scene,camera,landings[-1])
    pixel_error=math.hypot((a.x-b.x)*scene.render.resolution_x,(a.y-b.y)*scene.render.resolution_y)
    assert pixel_error<.01, pixel_error
    print('Closing corner alignment error (pixels):',pixel_error)
image_dir=OUT/'previews' if args.preview else OUT
image_dir.mkdir(exist_ok=True)
scene.render.filepath=str(image_dir/(tag+'.png'))
if not args.preview:
    bpy.ops.file.pack_all()
    bpy.ops.wm.save_as_mainfile(filepath=str(OUT/(tag+'.blend')))
bpy.ops.render.render(write_still=True)
if not args.preview:
    scene.render.image_settings.file_format='OPEN_EXR'
    scene.render.image_settings.color_depth='32'
    bpy.data.images['Render Result'].save_render(str(OUT/(tag+'.exr')), scene=scene)
    (OUT/(tag+'-info.json')).write_text(json.dumps({
        'renderer':'Blender '+bpy.app.version_string+' / Cycles',
        'max_samples':scene.cycles.samples,
        'adaptive_threshold':scene.cycles.adaptive_threshold,
        'denoised':scene.cycles.use_denoising,
        'width':scene.render.resolution_x,'height':scene.render.resolution_y,
        'png_bit_depth':16,'camera_type':camera.data.type,
        'perspective_geometry_correction':args.projection=='perspective',
        'orthographic_scale':camera.data.ortho_scale if camera.data.type=='ORTHO' else None,
        'image_generation':False,'composited':False,
        'textures_packed':all(i.packed_file for i in bpy.data.images if i.source=='FILE')
    },indent=2)+'\n')
print('FINISHED',tag)
