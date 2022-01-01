import { range } from "https://deno.land/x/lodash@4.17.15-es/lodash.js";

type Grid = string;
const LEFT = -1;
const RIGHT = 1;
const DOWN = 14;
const UP = -14;
export const directions = [LEFT, RIGHT, UP, DOWN] as const;
export type Direction = typeof directions[number];
const letters = ["A", "B", "C", "D"] as const;
type Letter = typeof letters[number];
const doorExits = [17, 19, 21, 23]; // Rule 1 cells

export interface State {
  readonly cost: number;
  readonly grid: Grid;
  readonly lastMovedCoord?: number;
  readonly lastMoveDirection?: Direction;
}
export const initialStatePart1: State = {
  cost: 0,
  grid: `#############
#...........#
###C#B#D#D###
  #B#C#A#A#  
  #########  `.replace(/\./g, "·"),
  lastMovedCoord: undefined,
  lastMoveDirection: undefined,
} as const;
export const initialStatePart2: State = {
  cost: 0,
  grid: `#############
#...........#
###C#B#D#D###
  #D#C#B#A#  
  #D#B#A#C#  
  #B#C#A#A#  
  #########  `.replace(/\./g, "·"),
  lastMovedCoord: undefined,
  lastMoveDirection: undefined,
} as const;

const costs = {
  A: 1,
  B: 10,
  C: 100,
  D: 1000,
} as const;

const targetColumns = {
  A: 3,
  B: 5,
  C: 7,
  D: 9,
} as const;

export function isLetter(char: string): char is Letter {
  return (letters as Readonly<string[]>).includes(char);
}

function tryMoveIntoRoom(coord: number, state: State): Direction | null {
  const cellMoving = state.grid[coord];
  if (!isLetter(cellMoving)) {
    throw Error("Can only move letters into rooms");
  }
  if (coord > DOWN * 2 && coord % DOWN !== targetColumns[cellMoving]) {
    // Can only move from corridord or final room into rooms
    return null;
  }
  if (
    // Some other letter in chamber
    range(1, 6).some(
      (i: number) =>
        isLetter(state.grid[targetColumns[cellMoving] + DOWN * i]) &&
        state.grid[targetColumns[cellMoving] + DOWN * i] != cellMoving,
    )
  ) {
    return null;
  }
  if (
    // Go down into final chamber
    coord % DOWN === targetColumns[cellMoving] &&
    state.grid[coord + DOWN] === "·"
  ) {
    return DOWN;
  }
  if (
    // Go right
    coord % DOWN < targetColumns[cellMoving] &&
    range(coord + RIGHT, targetColumns[cellMoving] + DOWN + 1).every(
      (c: number) => state.grid[c] === "·",
    )
  ) {
    return RIGHT;
  } else if (
    // Go left
    coord % DOWN > targetColumns[cellMoving] &&
    range(targetColumns[cellMoving] + DOWN, coord).every(
      (c: number) => state.grid[c] === "·",
    )
  ) {
    return LEFT;
  }
  return null;
}

export function afterMove(
  state: State,
  coord: number,
  direction: Direction,
): State {
  if (state.grid[coord + direction] != "·") {
    throw Error("Invalid move end");
  }
  const movingCell = state.grid[coord];
  if (!isLetter(movingCell)) {
    throw Error("Invalid move start");
  }
  const gridArr = [...state.grid];
  gridArr[coord + direction] = gridArr[coord];
  gridArr[coord] = "·";
  const newState: State = {
    cost: state.cost + costs[movingCell],
    grid: gridArr.join(""),
    lastMovedCoord: coord + direction,
    lastMoveDirection: direction,
  };
  return newState;
}

function isFinished(state: State, coord: number): boolean {
  const cellMoving = state.grid[coord] as Letter;
  return coord % DOWN === targetColumns[cellMoving] &&
    range(coord + DOWN, coord + DOWN * 5, DOWN).every((c: number) =>
      !isLetter(state.grid[c]) || state.grid[c] == cellMoving
    );
}

function childrenStates(state: State): State[] {
  const nextStates: State[] = [];
  if (state.lastMovedCoord !== undefined) {
    const move = tryMoveIntoRoom(state.lastMovedCoord, state);
    if (move !== null) {
      return [afterMove(state, state.lastMovedCoord, move)];
    }
  }
  if (
    state.lastMovedCoord !== undefined &&
    doorExits.includes(state.lastMovedCoord)
  ) { // Rule 1
    const startCoord = state.lastMovedCoord;
    if (!state.lastMoveDirection) {
      throw Error("Missing last move direction");
    }
    const directions = state.lastMoveDirection === UP
      ? [LEFT, RIGHT] as const
      : [state.lastMoveDirection];
    for (const dir of directions) {
      if (state.grid[startCoord + dir] !== "·") {
        continue;
      }
      nextStates.push(afterMove(state, startCoord, dir));
    }
    return nextStates;
  }
  if (
    // If moved up keep going up
    state.lastMovedCoord !== undefined && state.lastMoveDirection === UP &&
    state.lastMovedCoord > DOWN * 2
  ) {
    if (state.grid[state.lastMovedCoord + UP] !== "·") {
      return [];
    }
    return [afterMove(state, state.lastMovedCoord, UP)];
  }
  for (let startCoord = DOWN; startCoord < state.grid.length; startCoord++) {
    if (!isLetter(state.grid[startCoord])) {
      continue;
    }
    const move = tryMoveIntoRoom(startCoord, state);
    if (move !== null) {
      return [afterMove(state, startCoord, move)];
    }
    if (state.lastMovedCoord !== startCoord && startCoord < DOWN * 2) {
      continue;
    }
    if (isFinished(state, startCoord)) {
      continue;
    }
    for (const dir of [LEFT, RIGHT, UP] as const) {
      if (state.grid[startCoord + dir] !== "·") {
        continue;
      }
      nextStates.push(afterMove(state, startCoord, dir));
    }
  }
  return nextStates;
}

export function minCost(state: State, goalGrid: Grid): number | undefined {
  const sortedGoal = [...goalGrid].sort().join("");
  if ([...state.grid].sort().join("") != sortedGoal) {
    console.log(sortedGoal);
    console.log([...state.grid].sort().join(""));
    throw Error("Start and goal grid have different characters");
  }

  const frontier: Grid[] = [state.grid];
  const states: Map<Grid, State> = new Map();
  states.set(state.grid, state);
  let i = 0;
  while (frontier.length) {
    // Depth first is fine, we can explore all states anyway
    const state = states.get(frontier.pop()!)!;
    i++;
    for (const childState of childrenStates(state)) {
      const seenState = states.get(childState.grid);
      if (seenState === undefined || seenState.cost > childState.cost) {
        if (!frontier.includes(childState.grid)) {
          frontier.push(childState.grid);
        }
        states.set(childState.grid, childState);
      }
    }
  }
  return states.get(goalGrid)?.cost;
}

const targetPart1 = `#############
#...........#
###A#B#C#D###
  #A#B#C#D#  
  #########  `.replace(/\./g, "·");
const targetPart2 = `#############
#...........#
###A#B#C#D###
  #A#B#C#D#  
  #A#B#C#D#  
  #A#B#C#D#  
  #########  `.replace(/\./g, "·");

if (import.meta.main) {
  console.log(minCost(initialStatePart1, targetPart1));
  console.log(minCost(initialStatePart2, targetPart2));
}
