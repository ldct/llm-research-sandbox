import json,math
from pathlib import Path
import bpy
from mathutils import Vector
from bpy_extras.object_utils import world_to_camera_view
root=Path(__file__).resolve().parents[1]
pairs={
 '01-island-of-steps':((0,0,3),(4.55,-4.55,8.46)),
 '02-moon-palace':((-4,-1,4.85),(-.36,-4.64,9.218)),
 '03-impossible-frame-garden':((-4,2,3.1),(4,-6,12.7)),
}
checks=[]
for name,(a,b) in pairs.items():
 bpy.ops.wm.open_mainfile(filepath=str(root/'output/monuments'/f'{name}.blend'))
 s=bpy.context.scene
 assert s.camera.data.type=='ORTHO'
 assert s.render.engine=='CYCLES'
 assert s.cycles.samples==512
 assert (s.render.resolution_x,s.render.resolution_y)==(2400,2800)
 assert not s.camera.data.dof.use_dof
 assert not s.use_nodes
 audits=json.loads(s['collision_audits'])
 assert len(audits)>=2 and all(not a['intersections'] for a in audits)
 external=[i.name for i in bpy.data.images if i.source=='FILE' and not i.packed_file]
 assert not external,external
 bpy.context.view_layer.update()
 aa=world_to_camera_view(s,s.camera,Vector(a)); bb=world_to_camera_view(s,s.camera,Vector(b))
 error=math.hypot((aa.x-bb.x)*2400,(aa.y-bb.y)*2800)
 assert error<.01,error
 checks.append({'scene':name,'verified_camera':'ORTHO','renderer':s.render.engine,'packed_image_count':sum(bool(i.packed_file) for i in bpy.data.images),'mesh_objects':sum(o.type=='MESH' for o in s.objects),'passed_collision_checks':[a['check'] for a in audits],'alignment_error_pixels_after_reopening':error})
(root/'output/monuments/verification.json').write_text(json.dumps(checks,indent=2)+'\n')
print(json.dumps(checks,indent=2))
