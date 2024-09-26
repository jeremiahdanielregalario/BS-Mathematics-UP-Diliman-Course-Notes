# BS Mathematics UP Diliman Course Notes
Bachelor of Science in Mathematics Course Notes at UP Diliman


# ME13: Managing Lists

## Problem Statement

Create a program that will manage a list of integers. Note that this ME is equivalent to 300 points (3 MEs).

## Input

Input starts with a number $N$ and is followed by $N$ test cases. Each test cases will be consists of an initial list of positive integers (maybe empty), and a set of operations. The following are the operations:

`_1 x` => insert element x at the head of the list

`_2 x y` => insert element x after index y (if $y$ is greater than the current size of the list then no operation needs to be done.)

`_3 x` => delete the element at index x (if $x$ is greater than the current size of the list then no operation needs to be done.)

`_4 x` => delete all element $x$'s in the list

`_5` => print the list

Indexing will be zero based.

If the initial list is "`empty`" then that means that the list is initially empty.

## Output

The output will be the printed output everytime `_5` is called.

## Limits

$ 1 < N < 20 $
$ −100 < \text{input} \le 100 $

## Notes

Problems will have test cases that are not listed in their specification. Your solution must produce the right output for these *hidden test cases*.

### Sample Input #1

```c
3
1 2 3
_1 1
_1 2
_5
_2 3 2
_3 4
_5
_4 1
_5
empty
_5
_4 1
_4 2
_4 1 1
_5
4 2 5 6 4 3 2 1
_1 10
_2 3 5
_2 6 4
_5
```

### Sample Output #1

```c
2 1 1 2 3
2 1 1 2 3
2 2 3


10 4 2 5 6 6 4 3 3 2 1
```

