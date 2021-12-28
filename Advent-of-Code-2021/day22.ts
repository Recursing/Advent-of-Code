import * as _ from "./utils.ts";

type Range = Readonly<[number, number]>;
type Box = Readonly<[Range, Range, Range]>;

function parseLine(line: string): [boolean, Box] {
  const [word, rest] = line.split(" ");
  const ranges = rest.split(",");
  const box: _.DeepReadonly<number[][]> = ranges.map((r) =>
    r.split("=")[1].split("..").map(Number)
  );
  return [word == "on", box as Box];
}
const lines = _.readDay(22);
const commands = lines.map(parseLine);

const domain = _.range(-50, 51).map(
  () =>
    _.range(-50, 51).map(
      () => _.range(-50, 51).map(() => false),
    ),
);
const domainBox: Box = [[-50, 50], [-50, 50], [-50, 50]] as const;

function intersect(box1: Box, box2: Box): Box | null {
  function intersectRanges(range1: Range, range2: Range): Range | null {
    const start = Math.max(range1[0], range2[0]);
    const end = Math.min(range1[1], range2[1]);
    if (start > end) {
      return null;
    }
    return [start, end];
  }
  const intersections: Readonly<(Range | null)[]> = _.zip(box1, box2).map(
    ([r1, r2]) => intersectRanges(r1, r2),
  );
  if (intersections.some((i) => i == null)) {
    return null;
  }
  return intersections as Box;
}

for (const [isOn, box] of commands) {
  const intersection = intersect(box, domainBox);
  if (intersection == null) {
    continue;
  }
  const ranges = intersection.map((range) =>
    _.rangeInclusive(range[0], range[1])
  );

  for (
    const [x, y, z] of _.product3(...ranges as [number[], number[], number[]])
  ) {
    domain[x + 50][y + 50][z + 50] = isOn;
  }
}
console.log(domain.flat(2).filter((r) => r).length);

// Smart solution from reddit, just use signed volumes
// so you only need to compute intersections
const signedVolumes: [boolean, Box][] = [];
for (const [isOn, box] of commands) {
  for (const [otherIsOn, otherBox] of [...signedVolumes]) {
    const intersection = intersect(box, otherBox);
    if (intersection == null) {
      continue;
    }
    signedVolumes.push([!otherIsOn, intersection]);
  }
  if (isOn) {
    signedVolumes.push([true, box]);
  }
}
function volume(box: Box): number {
  return box.map((range) => Math.abs(range[1] - range[0]) + 1)
    .reduce((acc, n) => acc * n);
}

console.log(
  _.sum(signedVolumes.map(([isOn, box]) => isOn ? volume(box) : -volume(box))),
);
