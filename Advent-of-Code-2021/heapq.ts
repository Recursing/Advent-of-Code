// Partial port of python's heapq, copied basically verbatim, including some comments.
// All rights go to original the CPython developers

// For more comments and more functionality see the original cpython implementation

// A heap is a list of pairs, the first element of the pair is the priority
// (lowest priority will be at heap[0] and popped first)
export type Heap<T> = [number, T][];

export function heappush<T>(heap: Heap<T>, item: [number, T]) {
    heap.push(item);
    _siftdown(heap, 0, heap.length - 1);
}

export function heappop<T>(heap: Heap<T>): [number, T] | undefined {
    const lastelt = heap.pop();
    if (heap.length == 0) {
        return lastelt;
    }
    const returnitem = heap[0];
    heap[0] = lastelt!;
    _siftup(heap, 0);
    return returnitem;
}

function _siftdown<T>(heap: Heap<T>, startpos: number, pos: number): void {
    // 'heap' is a heap at all indices >= startpos, except possibly for pos.
    // pos is the index of a leaf with a possibly out-of-order value.
    // Restore the heap invariant.
    const newitem = heap[pos];
    // Follow the path to the root, moving parents down until finding a place
    // newitem fits.
    while (pos > startpos) {
        const parentpos = (pos - 1) >> 1;
        const parent = heap[parentpos];
        if (newitem[0] < parent[0]) {
            heap[pos] = parent;
            pos = parentpos;
            continue;
        }
        break;
    }
    heap[pos] = newitem;
}

function _siftup<T>(heap: Heap<T>, pos: number): void {
    // The python implementation minimizes comparisons, which we don't really need
    // but we'll copy it anyway
    const endpos = heap.length;
    const startpos = pos;
    const newitem = heap[pos];
    // Bubble up the smaller child until hitting a leaf.
    let childpos = 2 * pos + 1; // leftmost child position
    while (childpos < endpos) {
        // Set childpos to index of smaller child.
        const rightpos = childpos + 1;
        if (rightpos < endpos && heap[childpos][0] >= heap[rightpos][0])
            childpos = rightpos;
        // Move the smaller child up.
        heap[pos] = heap[childpos];
        pos = childpos;
        childpos = 2 * pos + 1;
        // The leaf at pos is empty now.Put newitem there, and bubble it up
        // to its final resting place(by sifting its parents down).
        heap[pos] = newitem;
    }
    _siftdown(heap, startpos, pos);
}
