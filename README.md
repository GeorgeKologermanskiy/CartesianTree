# CartesianTree

Дан массив целых чисел. Необходимо реализовать структуру данных, в которой требуется за О(log n) выполнять запросы:

сумма на подотрезке [l,r] (в задаче принята 0-индексация);
вставить элемент x в позицию pos (т.е. в результате вставки, элемент x должен оказаться pos-ым);
удалить элемент x, находящийся на позиции i;
присвоить элемент x на подотрезке [l, r];
прибавить число x на подотрезке [l, r];
next_permutation на подотрезке [l, r];
prev_permutation на подотрезке [l, r].
next_permutation и prev_permutation должны работать так же, как одноименные STL-алгоритмы; в частности, next_permutation([4, 3, 2, 1]) есть [1, 2, 3, 4], а не [4, 3, 2, 1]; аналогично, prev_permutation([1, 2, 2, 2, 3, 3, 4]) = [4, 3, 3, 2, 2, 2, 1].
Формат ввода
В первой строке записано число n (1 ≤ n ≤ 3*10^4) - количество элементов в массиве. Во второй строке записано n чисел, не превосходящих по модулю 3*10^4 - исходные значения элементов массива.

В третьей строке записано число q (1 ≤ q ≤ 10^5) - количество запросов. В последующих строках записаны сами запросы, по одному на каждой строке. Запросы задаются в следующем формате:

1 l r (0 ≤ l ≤ r < arraySize) - найти сумму всех чисел массива на отрезке [l, r];
2 x pos (|x| ≤ 3*10^4, 0 ≤ pos ≤ arraySize) - вставить элемент x на позицию pos;
3 pos (0 ≤ pos < arraySize) - удалить элемент x, находящийся на позиции pos;
4 x l r (|x| ≤ 3*10^4, 0 ≤ l ≤ r < arraySize) - присвоить элементам на подотрезке [l, r] число x;
5 x l r (|x| ≤ 3*10^4, 0 ≤ l ≤ r < arraySize) - прибавить к элементам на подотрезке [l, r] число x;
6 l r - выполнить next_permutation на подотрезке [l, r];
7 l r - выполнить prev_permutation на подотрезке [l, r]. В приведенном описании arraySize есть текущий размер массива.
Формат вывода
Для каждого запроса типа 1 выведите соответствующую сумму в отдельной строке.

По выполнении всех запросов, выведите итоговые значения элементов массива.
