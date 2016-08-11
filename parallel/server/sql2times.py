#!/usr/bin/env python
# -*- coding: utf-8 -*-

import sqlite3
import sys
import json
import pathlib

for arg in sys.argv[1:]:
    try:
        path_sql = pathlib.Path(arg).resolve()
    except FileNotFoundError:
        continue
    if not path_sql.is_file():
        continue
    total_time = 0
    conn = sqlite3.connect(str(path_sql))
    c = conn.cursor()
    names = [name[0] for name in c.execute('SELECT DISTINCT(name) FROM SolvingHistory;')]
    with open(str(path_sql.parent / (path_sql.stem + '.times')), 'w') as file_times:
        for name in names:
            ts_start = c.execute('select min(ts) '
                                 'from SolvingHistory '
                                 'where name = ? and event = "+";', (name,)).fetchone()[0]
            if (ts_start is None):
                print('Not even started: {}'.format(name))
                continue
            row_end = c.execute('select ts, data FROM SolvingHistory where id = (select min(id) '
                                'from SolvingHistory '
                                'where name = ? and event = "SOLVED");', (name,)).fetchone()
            if not row_end:
                print('Only started: {}'.format(name))
                continue
            ts_end, data = row_end
            data = json.loads(data)
            file_times.write('{} {} {}\n'.format(name, data['status'], ts_end - ts_start))
            total_time += ts_end - ts_start
    print('TOTAL: {} seconds'.format(total_time))
