import * as utils from "./utils.ts";
const instructions = utils.readDay(2);

// Straightforward solutions
let [horizontal, depth] = [0, 0];
for (const line of instructions) {
  const [direction, X] = line.split(" ");
  const amount = Number(X);
  switch (direction) {
    case "up":
      depth -= amount;
      break;
    case "down":
      depth += amount;
      break;
    case "forward":
      horizontal += amount;
      break;
  }
}
console.log(horizontal * depth);

horizontal = depth = 0;
let aim = 0;
for (const line of instructions) {
  const [direction, X] = line.split(" ");
  const amount = Number(X);
  switch (direction) {
    case "up":
      aim -= amount;
      break;
    case "down":
      aim += amount;
      break;
    case "forward":
      horizontal += amount;
      depth += aim * amount;
      break;
  }
}
console.log(horizontal * depth);

// Playing with types

const DIRECTIONS = ["forward", "up", "down"] as const;
type Direction = typeof DIRECTIONS[number];
const parseLine = (line: string): [Direction, number] => {
  const [direction, amount] = line.split(" ");
  if (!utils.isIn(DIRECTIONS, direction)) {
    throw Error(`"${direction}" is not a valid direction`);
  }
  return [direction, Number(amount)];
};

// part 1
const position = [0, 0];
const effects: {
  [K in Direction]: (amount: number, position_: typeof position) => void;
} = {
  forward: (amount, position) => (position[0] += amount),
  up: (amount, position) => (position[1] -= amount),
  down: (amount, position) => (position[1] += amount),
};

instructions
  .map(parseLine)
  .forEach(([direction, amount]) => effects[direction](amount, position));
console.log(position[0] * position[1]);

// part 2
const state = {
  horizontal: 0,
  depth: 0,
  aim: 0,
};
const newEffects: {
  [K in Direction]: (amount: number, state_: typeof state) => void;
} = {
  forward: (amount, state) => {
    state.horizontal += amount;
    state.depth += state.aim * amount;
  },
  up: (amount, state) => (state.aim -= amount),
  down: (amount, state) => (state.aim += amount),
};
instructions
  .map(parseLine)
  .forEach(([direction, amount]) => newEffects[direction](amount, state));
console.log(state.horizontal * state.depth);
