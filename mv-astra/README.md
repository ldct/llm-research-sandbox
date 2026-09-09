# Impossible architecture, physically rendered

The current work uses **Blender 4.5 / Cycles**, a Monte Carlo path tracer. Geometry, lights, materials, shadows, reflections and refractions are rendered from a 3D scene. The earlier `output/impossible-geometry/01-water-palace.png` is an image-generation exploration and is not a ray-traced render.

## Finished images

### Monument Valley scene studies

Three new scenes based on the [official Monument Valley screenshot gallery](https://store.steampowered.com/app/1927720/Monument_Valley/), rendered with actual orthographic cameras in Cycles:

| Render | Reference and interpretation | Editable scene |
| --- | --- | --- |
| [Island of Steps](output/monuments/01-island-of-steps.png) | [Rocky island reference](references/monument-valley/steam-07.jpg): warm rock outcrops, turquoise sea, mint copper pavilions, and a continuously ascending stair loop. | [Packed .blend](output/monuments/01-island-of-steps.blend) |
| [Moon Palace](output/monuments/02-moon-palace.png) | [Night palace reference](references/monument-valley/steam-00.jpg): three domes, stacked open loggias, a crescent sculpture, and stairs wrapping around a green marble tower. | [Packed .blend](output/monuments/02-moon-palace.blend) |
| [Impossible Frame Garden](output/monuments/03-impossible-frame-garden.png) | [Interlocking frames reference](references/monument-valley/steam-01.jpg): ivory and serpentine frames, circular brass sockets, and an orthogonal Penrose tribar over a reflecting pool. | [Packed .blend](output/monuments/03-impossible-frame-garden.blend) |

These are original architectural interpretations of the selected scenes, not exact level reconstructions. The descriptive render titles are not game chapter names. The source screenshots are stored for reference only and do not appear as textures in any render. Original image URLs are recorded in [steam-sources.json](references/monument-valley/steam-sources.json).

Each new image is **2400 × 2800**, 16-bit PNG, with a scene-linear 32-bit EXR beside it. Rendering uses up to 512 samples, adaptive sampling and denoising. Every scene includes beveled solid geometry, scanned surface maps, genuine open arches, metallic dome seams, refracting water, and physically evaluated lighting. The island additionally uses scanned rock meshes with their original UV textures and normal maps. Its foam follows the actual modeled waterline. No image generation, compositing, depth of field, or perspective deformation is used.

The two stair loops have endpoints separated along `(1, -1, 1.2)` and therefore coincident in the orthographic image. The ivory tribar uses three perpendicular beams with the same closing displacement. View-aligned mesh cuts resolve the foreground overlap. Each final scene records its measured endpoint alignment in its `-info.json`; shifting the camera exposes the deliberately open geometry.

The intersection cleanup reroutes landing rails around a single corner, adds openings at pavilion thresholds, relocates the island's upper bridge and carves rock clearance around the stairs. The palace tower now fits within the stair loop; its side chapel has a separate landing and grounded footing. The frame garden's upper upright is offset from both the approach stairs and the green frame. Evaluated mesh intersection checks cover these affected object groups and are recorded in each `-info.json` and packed scene; they are targeted checks, not a general structural or walkability simulation. Earlier PNGs, EXRs, Blender scenes and scripts are preserved in `output/monuments/before-intersection-fixes/`.

```sh
.tools/Blender.app/Contents/MacOS/Blender -b --python scripts/render_monuments.py -- --scene island --preview
.tools/Blender.app/Contents/MacOS/Blender -b --python scripts/render_monuments.py -- --scene island
.tools/Blender.app/Contents/MacOS/Blender -b --python scripts/render_monuments.py -- --scene palace
.tools/Blender.app/Contents/MacOS/Blender -b --python scripts/render_monuments.py -- --scene frames
.tools/Blender.app/Contents/MacOS/Blender -b --python scripts/render_monuments.py -- --scene frames --preview --reveal
```

Scene compositions are in [scripts/render_monuments.py](scripts/render_monuments.py). Shared modeling, materials, orthographic construction and rendering are in [scripts/monument_core.py](scripts/monument_core.py). `--samples` changes the final sample limit. Packed `.blend` scenes can be opened and rendered without the original asset directory.

### Courtyard studies

- [Orthographic daylight courtyard](output/cycles/daylight-orthographic.png) · [packed Blender scene](output/cycles/daylight-orthographic.blend)
- [Orthographic green marble at evening](output/cycles/evening-orthographic.png) · [packed Blender scene](output/cycles/evening-orthographic.blend)
- [Original perspective daylight](output/cycles/daylight.png) · [packed Blender scene](output/cycles/daylight.blend)
- [Original perspective evening](output/cycles/evening.png) · [packed Blender scene](output/cycles/evening.blend)

Full images are 2400 × 2056, 16-bit PNG. Rendering uses up to 512 samples per pixel, adaptive sampling, denoising, and AgX tone mapping. Scene-linear 32-bit EXRs are provided alongside the PNGs. Saved scenes are checked for missing external textures; all image textures are packed.

The orthographic versions use Blender's actual `ORTHO` camera and the unwarped stair geometry. Materials, lighting, camera direction, exposure, and rendering quality match the corresponding perspective versions. The courtyard and pool also use orthographic projection. The earlier perspective versions remain available for comparison.

[A shifted-camera preview](output/cycles/previews/daylight-reveal-preview.png) exposes the actual construction. Other working previews and render logs are in `output/cycles/previews/` and `output/cycles/logs/`.

## Render

This folder uses **Git LFS** for render images, Blender scenes, EXRs and binary material assets. After cloning the repository, run `git lfs install` and `git lfs pull` to retrieve them.

Blender 4.5 is required to regenerate the scenes. The local portable installation is in `.tools/Blender.app`; the application itself and download caches are not committed. On another machine, install Blender and substitute its executable (for example, `blender`) for the path below. Run commands from the `mv-astra/` project directory:

```sh
python3 scripts/fetch_materials.py
.tools/Blender.app/Contents/MacOS/Blender -b --python scripts/render_courtyard.py -- --preview
.tools/Blender.app/Contents/MacOS/Blender -b --python scripts/render_courtyard.py -- --variant daylight
.tools/Blender.app/Contents/MacOS/Blender -b --python scripts/render_courtyard.py -- --variant evening
.tools/Blender.app/Contents/MacOS/Blender -b --python scripts/render_courtyard.py -- --projection orthographic --variant daylight
.tools/Blender.app/Contents/MacOS/Blender -b --python scripts/render_courtyard.py -- --projection orthographic --variant evening
.tools/Blender.app/Contents/MacOS/Blender -b --python scripts/verify_monuments.py
```

Full renders save PNGs, scene-linear 32-bit EXRs, and `.blend` scenes with packed textures under `output/cycles/`. No image generation or image editing is used in the Cycles output. The script controls tone mapping through Blender's AgX view transform. `--samples` controls the sample limit; adaptive sampling may stop converged pixels earlier.

## How the geometry works

The staircase consists of four rising flights and five landings. It is an open structure in 3D, deliberately built so its two terminal landings project to the same place. Each flight has real stone tread geometry. From the locked camera, the staircase appears to climb around a closed loop. The stair geometry is designed in orthographic projection. `--projection orthographic` uses that geometry directly with a true orthographic camera. The default `--projection perspective` transforms the stair geometry to preserve its silhouette through a perspective camera (approximately 74 mm).

The first and last landing displacement determines the camera direction. Its component perpendicular to the viewing direction is checked numerically when the scene is built. Camera-aligned cuts in the foreground landing and the last flight allow the first rising treads and railings to appear in front at the closing corner. These are real cuts in the mesh; the image is not composited. This is an optical illusion for one viewpoint, rather than a globally impossible Euclidean solid. Moving the camera exposes the construction:

```sh
.tools/Blender.app/Contents/MacOS/Blender -b --python scripts/render_courtyard.py -- --preview --reveal
```

`--geometry-only` isolates the staircase for inspection. The scene's fixed illusion camera is named explicitly in the Blender file.

## References

- User's `mv.jpeg`: Monument Valley's camera, stairs, architectural rhythm, and visual depth contradictions.
- [ustwo: Monument Valley out now](https://ustwo.com/blog/monument-valley-out-now/): the creators' visual influences and design intent.
- [Ken Wong: The Art of Monument Valley, GDC 2015](https://gdcvault.com/play/1022299/The-Art-of-Monument): art direction and geometry.
- [Escher: Waterfall](https://escherinhetpaleis.nl/en/about-escher/masterpieces/waterfall): the continuous aqueduct paradox.
- [Escher: Belvedere](https://escherinhetpaleis.nl/en/about-escher/escher-today/belvedere): conflicting front/back connections.
- [Escher: Ascending and Descending](https://escherinhetpaleis.nl/en/about-escher/escher-today/ascending-and-descending): the rising closed staircase.
- [Thomas Schmidt: Escher-Penrose-Stairway](https://www.exergia.de/english/ideen-projekte/design-art/escher-penrose-stairway/): camera-dependent cuboid alignment.
- [PBRT gallery](https://www.pbrt.org/gallery): the requested physical rendering reference; especially the daylight pavilion and contemporary bathroom. The renders here use Cycles, not PBRT.
- [Blender Cycles](https://www.blender.org/features/rendering/): rendering engine.

Reference images under `references/` are retained for study with their respective original ownership. They are not textures in the rendered scene.

## Material sources

Scanned surface maps from Poly Haven, [CC0](https://polyhaven.com/license):

- [Marble 01](https://polyhaven.com/a/marble_01)
- [Concrete Floor 02](https://polyhaven.com/a/concrete_floor_02)
- [Plastered Wall 02](https://polyhaven.com/a/plastered_wall_02)
- [Potted Plant 01](https://polyhaven.com/a/potted_plant_01), instanced scanned plant model
- [Namaqualand Rocks 01](https://polyhaven.com/a/namaqualand_rocks_01), scanned rock geometry and UV surface maps used in the island

The water and bronze materials, geometry and sky illumination are configured in `scripts/render_courtyard.py`. Daylight uses light honed marble. Evening uses the same scanned surface with a dark green tint and a smoother finish, plus warm area lights in the portico.
