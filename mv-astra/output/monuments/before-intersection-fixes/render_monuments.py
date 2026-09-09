"""Three orthographic, physically path-traced studies of Monument Valley references.

blender -b --python scripts/render_monuments.py -- --scene island --preview
blender -b --python scripts/render_monuments.py -- --scene palace
blender -b --python scripts/render_monuments.py -- --scene frames

The render contains only real geometry and materials. Illusion joins are fixed
to the orthographic camera; --reveal exposes their open construction.
"""
import argparse
import sys
from pathlib import Path
sys.path.insert(0,str(Path(__file__).resolve().parent))
from monument_core import *

parser=argparse.ArgumentParser()
parser.add_argument('--scene',choices=['island','palace','frames'],default='island')
parser.add_argument('--preview',action='store_true')
parser.add_argument('--samples',type=int,default=512)
parser.add_argument('--reveal',action='store_true')
args=parser.parse_args(sys.argv[sys.argv.index('--')+1:] if '--' in sys.argv else [])
setup(args.preview,args.samples,portrait=True)
P=palette()
SOURCE='https://store.steampowered.com/app/1927720/Monument_Valley/'


def little_flag(pos,P,length=1.3):
    x,y,z=pos
    rod('Slender flagstaff',(x,y,z),(x,y,z+2.2),.016,P['bronze'])
    fabric=basic('Saffron silk banner',(.65,.17,.047),.65)
    p=fabric.node_tree.nodes.get('Principled BSDF'); p.inputs['Sheen Weight'].default_value=.35
    vv=[]; ff=[]
    for i in range(21):
        t=i/20
        for j in range(5):
            v=j/4
            vv.append((x+t*length,y+.12*math.sin(t*8-v)*t,z+2.1-.38*v-.16*t+.05*math.sin(t*7)))
    for i in range(20):
        for j in range(4):
            a=i*5+j; ff.append((a,a+5,a+6,a+1))
    o=mesh('Wind-shaped silk flag',vv,ff,fabric)
    solid=o.modifiers.new('Fabric thickness','SOLIDIFY'); solid.thickness=.002
    for p in o.data.polygons:p.use_smooth=True


def island():
    sea(size=150,deep=6.5,color=(.98,.995,1),wave=.095)
    # A fractured sandstone island, with pathways built around its narrow ridge.
    formations=[((5.4,1.1,.2),(13.4,10.4,4.2)),((7.25,3.2,4.2),(4.9,4.0,11.5)),((8.7,2.7,3.2),(3.4,3.6,7.9)),((5.7,3.7,3.7),(2.3,3.3,8)),((2.7,2.0,1.9),(4.0,3.5,5.4)),((7.8,-1.5,1.5),(3.7,3.7,5.1)),((2,-2.3,.5),(3.3,2.8,3.0)),((9.8,4.2,.7),(3,3.6,3.8)),((6,-4.1,.3),(3.4,3.1,3.9)),((.6,.6,.3),(2.9,3,3.4))]
    rocks=[scanned_rock('Scanned warm rock outcrop',loc,dims,i) for i,(loc,dims) in enumerate(formations)]
    shoreline(rocks,(5.4,1.1))
    # Ascending loop around the rock. Endpoints differ in depth but coincide in the camera.
    landings=impossible_stairs((0,0,3),P,base=-.6,rail=True)
    # Low arrival terrace, with an open arcade descending into the tide.
    box('Arrival terrace',(1.5,-3.9,.9),(4.8,2.2,.3),P['stone'])
    for x in (-.2,1.3,2.8):
        arch('Sea arcade',(x,-4.55),1.12,.4,-.25,.78,P['plaster'],base=-1.1,trim=P['stone'])
    stairs((-.25,-3.8,1.05),(-.25,-.85,3),1.25,P['stone'],P['bronze'],True)
    box('Lower landing',(-.25,-.4,2.85),(1.45,1.3,.3),P['stone'])
    pavilion('Arrival shrine',(-.3,-4.0,1.08),1.28,2.15,P)
    # Domed towers echo the delicate mint pavilions in the island reference.
    towers=[((11.55,.0,4.82),1.32,2.65),((10.45,7.0,5.73),1.35,2.65),((3.25,5.9,6.64),1.3,2.65)]
    for i,(pos,w,h) in enumerate(towers):
        x,y,z=pos
        banded_pier('Pavilion tower',x,y,-.5,z-.15,w*.87,P['jade'],P['stone'],P['grout'])
        pavilion('Island pavilion '+str(i),pos,w,h,P)
    # A narrow, real arched bridge to the highest sanctuary on the ridge.
    arch('High cliff bridge',(7.8,6.0),3.1,1.0,6.4,8.25,P['plaster'],base=3.5,trim=P['stone'])
    box('High bridge paving',(7.8,6,8.3),(3.65,1.1,.13),P['stone'])
    stairs((6.0,6.0,8.36),(6.0,3.75,10.1),1.1,P['stone'],P['bronze'],True)
    box('Summit dais',(6.1,3.05,10.1),(1.65,1.7,.28),P['stone'])
    pavilion('Summit lantern',(6.1,3.05,10.25),1.3,2.25,P)
    little_flag((5.5,2.45,10.27),P,1.1)
    # Square inlays, bronze studs and fine seams provide familiar construction scale.
    for x,y,z in ((1.1,-3.9,1.055),(2.6,-3.9,1.055),(10.45,0,4.824),(10.45,5.9,5.734),(4.55,5.9,6.644)):
        tile_square((x,y,z),1.08,P['jade'],P['bronze'],P['stone'])
    plant((2.8,-3.8,1.06),1.2,1)
    plant((11.5,.4,4.97),.72,2)
    sky(36,218,.48,-.9)
    camera((5.35,1.0,4.3),24.2)
    render('01-island-of-steps',args.preview,{'page':SOURCE,'image':'references/monument-valley/steam-07.jpg','motifs':'Sandstone island, sea, narrow stairways, mint domed pavilions'},[(landings[0],landings[-1])],args.reveal)


def palace():
    sea(size=180,deep=7,color=(.74,.85,.94),wave=.045)
    # A stepped stone base puts the palace in actual reflecting water.
    for dims,z in (((11,10,.55),.05),((9.8,8.8,.32),.47),((8.9,7.9,.2),.73)):
        box('Palace tidal foundation',(.25,.1,z),dims,P['darkjade'],.04)
    # Hollow lower tower: open arches, deep interiors and thick masonry.
    cx,cy=.45,.65
    for x,y,rot in ((cx,cy-1.8,0),(cx,cy+1.8,0),(cx-1.8,cy,math.pi/2),(cx+1.8,cy,math.pi/2)):
        arch('Great tower lower portal',(x,y),2.55,.5,3.75,6.25,P['jade'],rot,.83,P['stone'])
    for x in (-1.16,2.06):
        for y in (-.96,2.26):
            banded_pier('Tower corner pilaster',x,y,.82,6.3,.48,P['jade'],P['stone'],P['grout'])
    box('Tower middle cornice',(cx,cy,6.3),(4.1,4.1,.26),P['stone'])
    tile_square((cx,cy,6.44),3.7,P['jade'],P['bronze'],P['stone'])
    for x,y,rot in ((cx,cy-1.37,0),(cx,cy+1.37,0),(cx-1.37,cy,math.pi/2),(cx+1.37,cy,math.pi/2)):
        arch('Upper loggia',(x,y),2.03,.32,8.45,9.7,P['plaster'],rot,6.42,P['stone'])
    box('Upper belvedere terrace',(cx,cy,9.78),(3.4,3.4,.26),P['stone'])
    pavilion('Crown observatory',(cx,cy,9.93),2.5,3.25,P,True)
    little_flag((cx+1.28,cy+1.28,9.93),P,.95)
    # Multiple heights and deceptive wraparound stairs from the game reference.
    q=impossible_stairs((-4,-1,4.85),P,scale=.8,base=.82,rail=True)
    for p in q[1:4]:tile_square((p.x,p.y,p.z+.004),.9,P['jade'],P['bronze'],P['stone'])
    # Low side chapel, with a bridge carried by a single slender arch.
    pavilion('West chapel',(-4.4,2.2,4.7),1.45,2.4,P,True)
    banded_pier('West chapel tower',-4.4,2.2,.8,4.56,1.32,P['jade'],P['stone'],P['grout'])
    arch('West chapel bridge',(-2.8,2.2),1.7,.9,3.0,4.68,P['plaster'],base=.82,trim=P['stone'])
    pavilion('East chapel',(4.1,2.6,7.1),1.38,2.5,P,True)
    banded_pier('East chapel tower',4.1,2.6,.82,6.96,1.28,P['jade'],P['stone'],P['grout'])
    # Small door, inlaid bronze panels and battlements at human scale.
    for x in (-3.9,-2.9,2.9,3.9):
        box('Base battlement',(x,-3.5,1.35),(.48,.45,1),P['jade'])
    for x in (-3.2,3.2):
        tile_square((x,-2.5,.84),1.3,P['jade'],P['bronze'],P['stone'])
    for x,y,z in ((-1,-.8,1.0),(1.9,2.1,1.0),(.45,.65,6.45)):
        area('Amber portal lamp',(x,y,z+2),(x,y,z),95,(1,.45,.12),.45)
    plant((-3.6,-2.5,.85),1.3,1)
    plant((3,-2.6,.85),1.4,3)
    night()
    # A thin luminous crescent, modeled behind the palace, echoing its lunar backdrop.
    right=Vector((-DIRECTION.y,DIRECTION.x,0)).normalized(); up=DIRECTION.cross(right).normalized()
    center=Vector((.45,.65,9.7))-DIRECTION*8-right*1.7+up*2.4
    moon=basic('Pearlescent lunar sculpture',(.62,.71,.75),.25,.25)
    p=moon.node_tree.nodes.get('Principled BSDF'); p.inputs['Emission Color'].default_value=(.65,.75,1,1); p.inputs['Emission Strength'].default_value=.55
    verts=[]; faces=[]; radius=5
    for j in range(129):
        t=-math.pi/2+math.pi*j/128
        yy=radius*math.sin(t); xx=-radius*math.cos(t)
        inner=-radius*.72*math.cos(t)
        verts.extend([tuple(center+right*xx+up*yy),tuple(center+right*inner+up*yy)])
    for j in range(128):faces.append((j*2,j*2+1,j*2+3,j*2+2))
    moonobj=mesh('Crescent moon sculpture',verts,faces,moon)
    solid=moonobj.modifiers.new('Crescent thickness','SOLIDIFY'); solid.thickness=.04
    moonobj.visible_shadow=False
    camera((.25,.6,7),23.2)
    render('02-moon-palace',args.preview,{'page':SOURCE,'image':'references/monument-valley/steam-00.jpg','motifs':'Stacked open pavilions, onion domes, impossible stairs and a crescent moon'},[(q[0],q[-1])],args.reveal)


def frames():
    # Reinterpret the abstract frame level as monumental stonework in a quiet garden.
    sea(size=180,z=-.35,deep=3.5,color=(.74,.94,.87),wave=.017)
    for x in range(-11,12):
        for y in range(-12,10):
            # Water court with two broad paved edges and a rear portico.
            if -7<x<7 and -10<y<5:continue
            box('Garden travertine paving',(x*1.25,y*1.25,-.11),(1.244,1.244,.22),P['floor'],.008)
    box('Submerged garden foundation',(0,-2,-1.2),(30,30,.3),P['floor'])
    # Pale orthogonal tribar: X, -Y, +Z. Its distinct end vertices close in projection.
    a=Vector((-4,2,3.1)); b=a+Vector((8,0,0)); c=b+Vector((0,-8,0)); d=c+Vector((0,0,9.6))
    first=box('Ivory frame | horizontal return',(0,2,3.1),(9.1,1.1,1.32),P['stone'],.027)
    side=box('Ivory frame | lateral beam',(4,-2,3.1),(1.1,9.1,1.32),P['stone'],.027)
    terminal=box('Ivory frame | impossible vertical',(4,-6,7.9),(1.1,1.1,10.92),P['stone'],.027)
    # Preserve the rear beam silhouette at the upper corner of the foreground leg.
    sightline_cut([first],[terminal])
    # Feet and false terminal match form a three-right-angle closed frame.
    for x,y in ((4,-6),(4,2),(-4,2)):
        banded_pier('Frame pedestal',x,y,-1,2.45,1.05,P['darkjade'],P['bronze'])
    # A large polished green rectangular frame, standing across the ivory structure.
    # Its crossing is cut along the sightline so the nearer pillar appears to weave behind.
    frame=[]
    for x in (-5.8,5.8):frame.append(box('Serpentine vertical frame',(x,4.2,8.5),(.78,.85,10.8),P['darkjade'],.022))
    for z in (3.1,13.9):frame.append(box('Serpentine lintel',(0,4.2,z),(12.4,.85,.88),P['darkjade'],.022))
    for x in (-5.8,5.8):banded_pier('Green frame base',x,4.2,-.3,3.05,.8,P['darkjade'],P['bronze'])
    # Parallel ivory uprights connect the levels; a rotated doorway hints at changed gravity.
    box('Suspended ivory upright',(-4,2,8.2),(1.1,1.1,9.1),P['stone'],.025)
    box('Suspended ivory upper return',(-6,2,12.2),(5.1,1.1,1.32),P['stone'],.025)
    # Door-like recesses are actual recessed assemblies at the tower foot.
    portal=arch('Garden doorway',(4,-6.57),.66,.07,2.15,2.65,P['bronze'],base=.9)
    box('Recessed oxidized door',(4,-6.535,1.5),(.64,.045,1.4),P['dark'],.015)
    for x in (3.85,4.0,4.15):box('Bronze door flute',(x,-6.58,1.5),(.014,.023,1.33),P['bronze'],.002)
    for z in (5.1,6.3,7.5,8.7,9.9):
        # Rounded inset rings are a material translation of the game's manipulation sockets.
        bpy.ops.mesh.primitive_torus_add(major_radius=.135,minor_radius=.022,major_segments=48,minor_segments=12,location=(4,-6.558,z),rotation=(math.pi/2,0,0))
        o=bpy.context.object; o.name='Brass circular socket'; o.data.materials.append(P['bronze'])
    # A walkable landing and real stair flight give the abstract sculpture architectural scale.
    stairs((-4.1,-1.4,.06),(-4.1,1.2,3.77),1.12,P['stone'],P['bronze'],True,step_count=22)
    box('Footbridge to garden',(-4.1,-3,.06),(1.4,3.2,.22),P['stone'])
    tile_square((-4.1,-3.75,.175),1.25,P['jade'],P['bronze'],P['stone'])
    # Spare background colonnade and low benches recall the approved courtyard material study.
    for x in (-8,-3.5,1,5.5,10):
        arch('Distant garden arcade',(x,11.3),3.3,.65,2.8,5.2,P['plaster'],base=0,trim=P['stone'])
    box('Rear garden wall',(1,14.1,2.7),(29,.4,5.4),P['plaster'])
    box('Garden portico roof',(1,12.7,5.25),(29,3.7,.24),P['stone'])
    for x,y in ((-9,-4),(-9,3),(9,-5),(9,3),(-5,12),(5,12)):
        plant((x,y,.01),2.2,random.random()*6)
    for x,y in ((-9,-8),(9,-8)):
        box('Stone garden bench',(x,y,.5),(2.6,.65,.2),P['stone'],.035)
        for dx in (-.8,.8):box('Bench foot',(x+dx,y,.22),(.16,.4,.44),P['dark'],.015)
    sky(29,222,.48,-.95)
    camera((0,.9,6.1),25.2)
    render('03-impossible-frame-garden',args.preview,{'page':SOURCE,'image':'references/monument-valley/steam-01.jpg','motifs':'Interleaved ivory and dark green frames, upright paths, bronze circular sockets'},[(a,d)],args.reveal)


{'island':island,'palace':palace,'frames':frames}[args.scene]()
