import * as utils from "./utils.ts";
//  target area: x=79..137, y=-176..-117

const minY = -176;
const maxY = -117;

function checkY(dy0: number): boolean {
  let y = 0;
  let dy = dy0;
  while (y > maxY) {
    y += dy;
    dy -= 1;
  }
  return y >= minY;
}

const validDys = utils.range(-minY + 1).filter(checkY);
const maxvalidDy = validDys[validDys.length - 1];
console.log(maxvalidDy * (maxvalidDy + 1) / 2);

const minX = 79;
const maxX = 137;

function checkVelocity([dx0, dy0]: [number, number]): boolean {
  let x = 0;
  let y = 0;
  let dx = dx0;
  let dy = dy0;
  while ((x < minX && dx > 0) || y > maxY) {
    x += dx;
    dx -= +(dx > 0);
    y += dy;
    dy -= 1;
  }
  return x >= minX && x <= maxX && y >= minY && y <= maxY;
}

console.log(
  utils.product(utils.range(0, maxX, true), utils.range(minY, -minY, true))
    .filter(
      checkVelocity,
    ).length,
);
