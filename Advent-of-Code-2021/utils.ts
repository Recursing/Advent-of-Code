// built-ins I miss from python
// don't want to import lodash but maybe I should, it has everything here

export function sum(array: (number | boolean)[]): number {
  return array.reduce<number>((a, b) => a + +b, 0);
}

export function range(end: number): number[] {
  return [...Array(end).keys()];
}

export function zip<T>(...args: T[][]): T[][] {
  const minLength = Math.min(...args.map((arr) => arr.length));
  return range(minLength).map((i) => args.map((arr) => arr[i]));
}

export async function readDay(n: number): Promise<string[]> {
  const paddedN = String(n).padStart(2, "0");
  return (await Deno.readTextFile(`./day${paddedN}.txt`)).split("\n");
}
