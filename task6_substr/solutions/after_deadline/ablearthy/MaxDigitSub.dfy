opaque predicate IsDigit(ch: char)
// {
//     '0' <= ch && ch <= '9'
// }

// ∀ x ∈ a[m..n) → IsDigit(x)
function AllDigits(a: array<char>, m: int, n: int): bool
    requires 0 <= m <= n <= a.Length
    reads a
{
    if m == n then true
    else IsDigit(a[n - 1]) && AllDigits(a, m, n-1)
}

// Length of the half-open interval [m..n) is (n - m)
ghost function IntervalLength(m: int, n: int): int {
    n - m
}


// a[k..m) is the leftmost maximum-length subarray containing only digits
method MaxDigitSub(a: array<char>)
    returns (k: int, m: int)
    ensures 0 <= k <= m <= a.Length && AllDigits(a, k, m)
    ensures forall p, q ::
        // For any subarray a[p..q) containing only digits:
        0 <= p <= q <= a.Length && AllDigits(a, p, q) ==>
        //   - either a[k..m) is longer: IntervalLength(k, m) > IntervalLength(p, q)
        //   - or they have equal length and a[k..m) is leftmost: IntervalLength(p, q) == IntervalLength(k, m) && k <= p
        IntervalLength(k, m) > IntervalLength(p, q) || (IntervalLength(p, q) == IntervalLength(k, m) && k <= p)
{
    k, m := 0, 0;
    var leftIdx, idx, prevIsDigit :=  0, 0, true;
    while idx < a.Length
    invariant 0 <= k <= leftIdx <= idx <= a.Length && AllDigits(a, leftIdx, idx)
    invariant 0 <= k <= m <= idx <= a.Length && AllDigits(a, k, m)
    invariant prevIsDigit || idx == leftIdx
    invariant forall leftIdx' ::
        (0 <= leftIdx' <= idx && AllDigits(a, leftIdx', idx)) ==> leftIdx <= leftIdx'
    invariant forall p, q ::
        0 <= p <= q <= idx && AllDigits(a, p, q) ==>
        m - k > q - p || (q - p == m - k && k <= p)
    {
        leftIdx, idx, prevIsDigit := (if IsDigit(a[idx]) then (if prevIsDigit then leftIdx else idx) else (idx + 1)), idx + 1, IsDigit(a[idx]);

        if idx - leftIdx > m - k {
            k, m := leftIdx, idx;
        }
    }
}
