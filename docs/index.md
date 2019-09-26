## OpenSMT Solver

### Description

### Manual:
To get a model for a SAT formula we use `get-value ()` and specify the desired terms for within that: For e.g,  
`(get-value (x y))` will print the value for x and y.


Interpolation:
LRA interpolation algorithms can be changed with the follwing option in the command line:

`(set-option :interpolation-lra-algorithm <N>)`
where N can be:
 0 for Farkas interpolation
 2 for dual Farkas interpolation
 4 for decomposed interpolants
 5 for dual decomposed interpolants
 3 for no-man's land algorithm

For the flexible no-man's land algorithm we can alter the interpolant within the interval `[0 , 1)`  
To do so, the following option can be used:
 `(set-option :interpolation-lra-factor "1/5")`

### news

{% for news in site.news  %}
- {{ news.newsdate | date_to_string }} [{{news.title}}]({{ news.url }})
{% endfor %}

