"""
This script is meant to be run with blender (https://www.blender.org/download/).
Save your input as day22.txt and run `blender --background --python day22.py`
in the same folder.
No need to pip install bpy or bmesh.

The 'calc_volume' method uses C doubles which might not be precise enough for
this problem (since the solution for part 2 has 15 digits), but seems to be
good enough for my input
"""

import bpy
import bmesh

# Delete default cube
bpy.data.meshes.remove(bpy.data.objects["Cube"].data)


def parse_line(line: str):
    state, rest = line.split(" ")
    ranges = [r.split("=")[1].split("..") for r in rest.split(",")]
    ranges = [(float(r[0]), float(r[1])) for r in ranges]
    # Center of the box
    location = tuple((r[0] + r[1]) / 2 for r in ranges)
    # Dimensions of the box, +1 is needed because ranges are inclusive
    size = tuple(abs(r[1] - r[0]) + 1 for r in ranges)
    return state == "on", (location, size)


actions = list(map(parse_line, open("day22.txt")))

first_state, (location, scale) = actions.pop(0)
assert first_state, "First cube is not on"

bpy.ops.mesh.primitive_cube_add(size=1, location=location, scale=scale)
main_mesh = bpy.data.objects["Cube"]
main_mesh.name = "main_mesh"

for (state, (location, scale)) in actions:
    bpy.ops.mesh.primitive_cube_add(size=1, location=location, scale=scale)
    modifier = main_mesh.modifiers.new(name="Boolean", type="BOOLEAN")
    modifier.operation = "UNION" if state else "DIFFERENCE"
    modifier.object = bpy.data.objects["Cube"]
    bpy.context.view_layer.objects.active = main_mesh
    bpy.ops.object.modifier_apply(modifier="Boolean")
    bpy.data.meshes.remove(bpy.data.objects["Cube"].data)

bm = bmesh.new()
bm.from_mesh(main_mesh.data)
part_2 = bm.calc_volume()

# Part 1, intersect with small cube in the center
bpy.ops.mesh.primitive_cube_add(size=1, location=(0, 0, 0), scale=(101, 101, 101))
modifier = main_mesh.modifiers.new(name="Boolean", type="BOOLEAN")
modifier.operation = "INTERSECT"
modifier.object = bpy.data.objects["Cube"]
bpy.context.view_layer.objects.active = main_mesh
bpy.ops.object.modifier_apply(modifier="Boolean")
bpy.data.meshes.remove(bpy.data.objects["Cube"].data)

bm = bmesh.new()
bm.from_mesh(main_mesh.data)
part_1 = bm.calc_volume()
print(f"Part 1: {part_1}")
print(f"Part 2: {part_2}")
