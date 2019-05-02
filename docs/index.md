## OpenSMT Solver

### Description

### news

{% for news in site.news  %}
- {{ news.newsdate | date_to_string }} [{{news.title}}]({{ news.url }})
{% endfor %}

