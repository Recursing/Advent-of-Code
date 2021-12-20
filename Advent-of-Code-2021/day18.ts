import * as utils from "./utils.ts";
import { assert } from "https://deno.land/std@0.117.0/testing/asserts.ts";
type Node = {
  value: number;
  previous?: Node;
  next?: Node;
};
type NodePair = [NodePair | Node, NodePair | Node];
type NumberPair = [number | NumberPair, number | NumberPair];
const isPair = Array.isArray;

function explode(pair: NodePair | Node, depth = 1): boolean {
  if (!isPair(pair)) {
    return false;
  }
  if (depth <= 3) {
    return explode(pair[0], depth + 1) || explode(pair[1], depth + 1);
  }
  for (const [i, child] of pair.entries()) {
    if (!isPair(child)) {
      continue;
    }
    const [l, r] = child;
    assert(!isPair(l) && !isPair(r));
    const newNode = { value: 0, previous: l.previous, next: r.next };
    if (l.previous) {
      l.previous.value += l.value;
      l.previous.next = newNode;
    }
    if (r.next) {
      r.next.value += r.value;
      r.next.previous = newNode;
    }
    pair[i] = newNode;
    return true;
  }
  return false;
}

function split(pair: NodePair): boolean {
  for (const [i, child] of pair.entries()) {
    if (isPair(child)) {
      if (split(child)) {
        return true;
      }
      continue;
    }
    if (child.value >= 10) {
      const val1: Node = {
        previous: child.previous,
        value: Math.floor(child.value / 2),
      };
      const val2: Node = {
        value: Math.ceil(child.value / 2),
        next: child.next,
      };
      val1.next = val2;
      val2.previous = val1;
      if (val1.previous) {
        val1.previous.next = val1;
      }
      if (val2.next) {
        val2.next.previous = val2;
      }
      pair[i] = [val1, val2];
      return true;
    }
  }
  return false;
}

function wrap(pair: NodePair): ParseResult {
  let first: Node | NodePair = pair;
  while (isPair(first)) {
    first = first[0];
  }
  let last: Node | NodePair = pair;
  while (isPair(last)) {
    last = last[1];
  }
  return { first, last, content: pair };
}

function add(pair1: ParseResult, pair2: ParseResult): ParseResult {
  pair1 = structuredClone(pair1);
  pair2 = structuredClone(pair2);
  pair1.last.next = pair2.first;
  pair2.first.previous = pair1.last;
  const res: NodePair = [pair1.content, pair2.content];
  while (explode(res) || split(res));
  return wrap(res);
}

type ParseResult = { first: Node; content: NodePair; last: Node };
function parse(pair: NumberPair): ParseResult {
  const [l, r] = pair;
  type IntermediateResult =
    | ParseResult
    | utils.Replace<ParseResult, "content", Node>;
  let resultL: IntermediateResult;
  let resultR: IntermediateResult;

  if (isPair(l)) {
    resultL = parse(l);
  } else {
    const nodeL = { value: l };
    resultL = { content: nodeL, first: nodeL, last: nodeL };
  }
  if (isPair(r)) {
    resultR = parse(r);
  } else {
    const nodeR = { value: r };
    resultR = { content: nodeR, first: nodeR, last: nodeR };
  }
  resultL.last.next = resultR.first;
  resultR.first.previous = resultL.last;
  return {
    content: [resultL.content, resultR.content],
    first: resultL.first,
    last: resultR.last,
  };
}

const numbers: NumberPair[] = utils.readDay(18).map((r) => JSON.parse(r));

function magnitude(pairOrNode: NodePair | Node): number {
  if (!isPair(pairOrNode)) {
    return pairOrNode.value;
  }
  const [l, r] = pairOrNode;
  return 3 * magnitude(l) + 2 * magnitude(r);
}

console.log(
  magnitude(numbers.map(parse).reduce(add).content),
);

console.log(
  Math.max(
    ...utils.pairs(numbers.map(parse))
      .flatMap(([a, b]) => [add(a, b), add(b, a)])
      .map((r) => magnitude(r.content)),
  ),
);
