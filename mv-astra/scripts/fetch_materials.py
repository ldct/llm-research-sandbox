"""Download the small set of CC0 Poly Haven textures used by the scene."""
from pathlib import Path
import concurrent.futures
import json
import subprocess

ROOT = Path(__file__).resolve().parents[1]
DEST = ROOT / 'assets' / 'textures'
DEST.mkdir(parents=True, exist_ok=True)

def fetch(asset):
    data = json.loads(subprocess.check_output([
        'curl', '-fsSL', f'https://api.polyhaven.com/files/{asset}']))
    result = {}
    for key in ('Diffuse', 'Rough', 'nor_gl', 'Displacement'):
        variants = data[key]['2k']
        info = variants.get('jpg') or variants.get('png')
        url = info['url']
        path = DEST / url.rsplit('/', 1)[-1]
        if not path.exists():
            subprocess.run(['curl', '-fsSL', url, '-o', str(path)], check=True)
        result[key] = str(path.relative_to(ROOT))
    return asset, result

with concurrent.futures.ThreadPoolExecutor(max_workers=3) as executor:
    manifest = dict(executor.map(fetch, ['marble_01', 'concrete_floor_02', 'plastered_wall_02']))
(DEST / 'manifest.json').write_text(json.dumps(manifest, indent=2) + '\n')
print(json.dumps(manifest, indent=2))

# Scanned plant and rock geometry used by the courtyard and island studies.
jobs = []
for asset in ('potted_plant_01', 'namaqualand_rocks_01', 'namaqualand_cliff_01'):
    data = json.loads(subprocess.check_output([
        'curl', '-fsSL', f'https://api.polyhaven.com/files/{asset}']))['gltf']['2k']['gltf']
    model_dir = ROOT / 'assets' / asset
    jobs.append((data['url'], model_dir / f'{asset}_2k.gltf'))
    jobs += [(item['url'], model_dir / name) for name,item in data['include'].items()]
def download_model_file(job):
    url,path = job
    path.parent.mkdir(parents=True, exist_ok=True)
    if not path.exists():
        subprocess.run(['curl','-fsSL',url,'-o',str(path)], check=True)
with concurrent.futures.ThreadPoolExecutor(max_workers=5) as executor:
    list(executor.map(download_model_file, jobs))
