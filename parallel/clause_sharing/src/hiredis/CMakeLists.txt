add_library(hiredis STATIC
        "hiredis.c"
        "async.c"
        "dict.c"
        "net.c"
        "sds.c"
        "read.c"
        )