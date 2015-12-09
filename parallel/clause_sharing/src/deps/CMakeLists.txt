add_library(hiredis STATIC
        "${SRC_HIREDIS}/hiredis.c"
        "${SRC_HIREDIS}/async.c"
        "${SRC_HIREDIS}/dict.c"
        "${SRC_HIREDIS}/net.c"
        "${SRC_HIREDIS}/sds.c"
        )