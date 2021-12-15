import * as utils from "./utils.ts";
import * as heapq from "./heapq.ts";

const grid: number[][] = utils.readDay(15).map((line) => [...line].map(Number));

function solve(grid: number[][]) {
    const distances = grid.map((row) => row.map(() => Infinity));
    distances[0][0] = 0;
    const height = grid.length;
    const width = grid[0].length;

    const frontier: heapq.Heap<[number, number]> = [[0, [0, 0]]];
    while (frontier.length) {
        const [cost, [y, x]] = heapq.heappop(frontier)!;
        for (const [ny, nx] of utils.neighbors(y, x, height, width)) {
            if (distances[ny][nx] > grid[ny][nx] + cost) {
                const newCost = grid[ny][nx] + cost;
                distances[ny][nx] = newCost;
                heapq.heappush(frontier, [newCost, [ny, nx]]);
            }
        }
    }
    return distances[height - 1][width - 1];
}
console.log(solve(grid));

const bigGrid = utils.range(5)
    .flatMap((i) => grid.map((row) =>
        utils.range(5).flatMap((j) => row.map((n) => ((n + i + j - 1) % 9) + 1))
    ));
console.log(solve(bigGrid));