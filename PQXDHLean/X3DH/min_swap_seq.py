# For arbitrary swaps, the answer is still cycle decomposition in O(n). The actual sequence of swaps falls directly out of the cycles:
# For each cycle of length k, you need exactly k − 1 swaps. To extract the swaps, just walk each cycle and swap each element back to its correct position.


def min_swaps_sequence(source, target):
    # Build the "difference" permutation: where does each element need to go?
    pos = {v: i for i, v in enumerate(source)}
    perm = [pos[t] for t in target]  # perm[i] = where target[i] currently sits in source

    visited = [False] * len(perm)
    swaps = []

    for i in range(len(perm)):
        if visited[i] or perm[i] == i:
            visited[i] = True
            continue
        # Walk the cycle
        j = i
        while not visited[j]:
            visited[j] = True
            nxt = perm[j]
            if nxt != i:
                swaps.append((i, nxt))  # swap positions i and nxt in source
                # Apply the swap to perm so it stays consistent
                perm[j], perm[nxt] = perm[nxt], perm[j]
            j = nxt

    return swaps