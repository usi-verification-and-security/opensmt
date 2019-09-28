**Interpolation:**
LRA interpolation algorithms can be changed with the following option in the command line:

`(set-option :interpolation-lra-algorithm <N>)`
where N can be:
- 0 for Farkas interpolation [TACAS'04](https://link.springer.com/chapter/10.1007/978-3-540-24730-2_2)
- 2 for dual Farkas interpolation
- 4 for decomposed interpolants [TACAS'19](https://link.springer.com/chapter/10.1007/978-3-030-17462-0_1)
- 5 for dual decomposed interpolants [TACAS 2019](https://link.springer.com/chapter/10.1007/978-3-030-17462-0_1)
- 3 for no-man's land algorithm [HVC'17](https://link.springer.com/chapter/10.1007/978-3-319-70389-3_13)

For the flexible no-man's land algorithm we can alter the interpolant within the interval `alpha = [0 , 1)`  
To do so, the following option can be used:
 `(set-option :interpolation-lra-factor "alpha")`

An example for demonstration purpose:
```
(set-logic QF_LRA)
(set-option :produce-interpolants true)
(set-option :interpolation-lra-algorithm 3) ;to specify interpolation Alg
(set-option :interpolation-lra-factor "1/5") ;to specify alpha
(declare-fun x () Real)
(declare-fun y () Real)
(declare-fun z () Real)

(assert (!(<= 1 (+ (* 2 x) y (* 3 z) ) ) :named A)) ;to specify partition A
(assert (!(<= 3  (+ (* (- 1) x) (* (- 1) y) (* (- 1) z))) :named B)) ;to specify partition B
(assert (!(<= 0 (+ x (* 3 y) (* (- 1) z) ) ) :named C))
(check-sat)
(get-interpolants A (and B C)) 
```
To get a model for a SAT formula we use `get-value ()` and specify the desired terms. For e.g,  
`(get-value (x y))` will print the value for x and y.
