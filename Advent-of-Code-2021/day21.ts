import * as _ from "./utils.ts";
// Player 1 starting position: 2
// Player 2 starting position: 10

const die = {
  value: 100,
  rolls: 0,
  roll() {
    this.value++;
    this.rolls++;
    if (this.value > 100) {
      this.value -= 100;
    }
    return this.value;
  },
};

const board = {
  position1: 2,
  position2: 10,
  score1: 0,
  score2: 0,
  score: 0,
  gameOver: false,
  play() {
    let dieResult = _.sum(_.range(3).map(() => die.roll()));
    this.position1 = (this.position1 + dieResult - 1) % 10 + 1;
    this.score1 += this.position1;
    if (this.score1 >= 1000) {
      this.gameOver = true;
      this.score = die.rolls * this.score2;
      return;
    }
    dieResult = _.sum(_.range(3).map(() => die.roll()));
    this.position2 = (this.position2 + dieResult - 1) % 10 + 1;
    this.score2 += this.position2;
    if (this.score2 >= 1000) {
      this.gameOver = true;
      this.score = die.rolls * this.score1;
    }
  },
};

while (!board.gameOver) {
  board.play();
}
console.log(board.score);

const board2 = {
  position1: 2,
  position2: 10,
  score1: 0,
  score2: 0,
  turn: 0,
};
type Board = typeof board2;

function hash(board: typeof board2): number {
  // All numbers are small enough for this to always fit in a js exact int
  return _.sum(
    Object.values(board)
      .map((value, index) => 50 ** index * value),
  );
}
const cache: Record<number, [number, number]> = {};

function chances(board: Board): [number, number] {
  const boardHash = hash(board);
  if (cache[boardHash]) {
    return cache[boardHash];
  }
  if (board.score1 >= 21) {
    return [1, 0];
  }
  if (board.score2 >= 21) {
    return [0, 1];
  }
  const nextTurn = (board.turn + 1) % 6;
  const res: [number, number] = [0, 0];
  for (const result of _.range(1, 4)) {
    let position1 = board.position1;
    let score1 = board.score1;
    let position2 = board.position2;
    let score2 = board.score2;
    if (board.turn < 3) {
      position1 = (position1 + result - 1) % 10 + 1;
    } else {
      position2 = (position2 + result - 1) % 10 + 1;
    }
    if (nextTurn == 3) {
      score1 = score1 + position1;
    } else if (nextTurn == 0) {
      score2 = score2 + position2;
    }
    const nextChances = chances({
      position1,
      position2,
      score1,
      score2,
      turn: nextTurn,
    });
    res[0] += nextChances[0];
    res[1] += nextChances[1];
  }
  cache[boardHash] = res;
  return res;
}
console.log(chances(board2));
