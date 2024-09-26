# BS Mathematics UP Diliman Course Notes
Bachelor of Science in Mathematics Course Notes at UP Diliman


# ME3: Multiplying Binomials

## Problem Statement

Given three binomials, the goal of this exercise is to compute for the product of the three binomials.

## Input

Input starts with a number $N$ and is followed by $N$ set of $6$ integers $(a_1, b_1, a_2, b_2, a_3, b_3)$ (pertaining to $a_ix+bi$).

## Output

The output is the product of the three binomials, presented as $p_3, p_2, p_1, p_0$ (pertaining to $p_3x^3+p_2x^2+p_1x+p_0$)

## Limits

$ 1 < N < 20 $
$ −100 \le A_i \le 100 $

## Notes

Problems will have test cases that are not listed in their specification. Your solution must produce the right output for these *hidden test cases*.

### Sample Input #1

```c
4
1 2 3 -1 2 3
-1 0 1 0 -1 0
0 1 0 2 0 3
2 3 1 -10 -5 3
```

### Sample Output #1

```c
6 19 11 -6
1 0 0 0
0 0 0 6
-10 91 99 -90
```
