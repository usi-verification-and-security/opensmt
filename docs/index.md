## OpenSMT Solver

### Description

### Manual:
To get a model for a SAT formula we use `get-value ()` and specify the desired terms for within that: For e.g,  
`(get-value (x y))` will print the value for x and y.


**Interpolation:**
LRA interpolation algorithms can be changed with the follwing option in the command line:

`(set-option :interpolation-lra-algorithm <N>)`
where N can be:
- 0 for Farkas interpolation
- 2 for dual Farkas interpolation
- 4 for decomposed interpolants
- 5 for dual decomposed interpolants
- 3 for no-man's land algorithm

For the flexible no-man's land algorithm we can alter the interpolant within the interval `alpha = [0 , 1)`  
To do so, the following option can be used:
 `(set-option :interpolation-lra-factor "alpha")`

An example for demonstration purpose:
```
(set-logic QF_LRA)
(set-option :produce-interpolants true)
(set-option :interpolation-lra-algorithm 3) ;//to specify interpolation Alg
(set-option :interpolation-lra-factor "1/5") ;//to specify alpha
(declare-fun x () Real)
(declare-fun y () Real)
(declare-fun z () Real)

(assert (!(<= 1 (+ (* 2 x) y (* 3 z) ) ) :named A)) ;//to specify partition A
(assert (!(<= 3  (+ (* (- 1) x) (* (- 1) y) (* (- 1) z))) :named B))
(assert (!(<= 0 (+ x (* 3 y) (* (- 1) z) ) ) :named C))
(check-sat)
(get-interpolants A (and B C)) 
```
### news

{% for news in site.news  %}
- {{ news.newsdate | date_to_string }} [{{news.title}}]({{ news.url }})
{% endfor %}

