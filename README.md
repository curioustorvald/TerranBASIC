Terran BASIC is a dialect of BASIC which embraces the concept of functional programming. In other words: *BASIC and Haskell living together, mass hysteria!*

Details of the language is fully described in `tbasman.pdf`, please check out!

## Sample Programs

Terran BASIC is mostly compatible with traditional BASIC, so you can just forgo all the functional goodies and do this:

```
10 FOR I=1 TO 20
20 PRINT SPC(20-I);
30 FOR J=1 TO I*2-1
40 PRINT "*";
50 NEXT
60 PRINT
70 NEXT
```

But with Terran BASIC you can do, I don't know, recursion:

```
10 DEFUN FAC(N)=IF N==0 THEN 1 ELSE N*FAC(N-1)
20 FOR K=1 TO 10
30 PRINT FAC(K)
40 NEXT
```

...or `MAP`ing that `FAC` function:

```
10 DEFUN FAC(N)=IF N==0 THEN 1 ELSE N*FAC(N-1)
20 K=MAP(FAC, 1 TO 10)
30 PRINT K
```

...or how about writing your own `APPLY`ing:

```
10 DEFUN APPLY(F,X)=F(X)
20 DEFUN FUN(X)=X^2
30 K=APPLY(FUN,42)
40 PRINT K
```

...or a closure with currying:

```
10 F=[K]~>[T]~>ABS(T)==K
20 CF=F(32)
30 PRINT CF(24) : REM will print 'false'
40 PRINT CF(-32) : REM will print 'true'
```

...or use a monad to add a memoisation to your function:

```
10 FIB=[N,M]~>IF M==UNDEFINED THEN FIB(N,MRET(1!1!NIL))
    ELSE IF LEN(MJOIN(M))>=N THEN HEAD(MJOIN(M))
    ELSE FIB(N,M>>=([XS]~>MRET((XS(0)+XS(1))!XS)))
100 FOR K=1 TO 10
110 PRINT FIB(K);" ";
120 NEXT
```

...or writing a Quicksort in one-liner!

```
10 QSORT=[XS]~>IF LEN(XS)<1 THEN NIL ELSE
    QSORT(FILTER([X]~>X<HEAD XS,TAIL XS)) # HEAD(XS)!NIL #
    QSORT(FILTER([X]~>X>=HEAD XS,TAIL XS))
100 L=7!9!4!5!2!3!1!8!6!NIL
110 PRINT L
120 PRINT QSORT(L)
```

## Open-Source Acknowledgement

The reference implementation of the Terran BASIC runs on the [TSVM](https://github.com/curioustorvald/tsvm), which runs on Java Version 8 **only** with graphics processor capable of OpenGL 2+.
