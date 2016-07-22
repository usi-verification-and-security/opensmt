(set-logic QF_LRA)
(declare-fun tim.monitor_state.6__AT1 () Bool)
(declare-fun tim.monitor_state.7__AT1 () Bool)
(assert
 (let ((.def_1429 (not tim.monitor_state.6__AT1)))
 (let ((.def_1428 (not tim.monitor_state.7__AT1)))
 (let ((.def_1430 (or .def_1428 .def_1429)))
 (let ((.def_1433 (or .def_1430 false)))
 (let ((.def_1439 (or .def_1433 false)))
 (let ((.def_1442 (and .def_1439 true)))
 (let ((.def_1514 (and .def_1442 true)))
 (let ((.def_1515 (and true .def_1514)))
 (let ((.def_1516 (and true .def_1515)))
 (let ((.def_9196 (and .def_1516 true)))
 (let ((.def_9197 (and true .def_9196)))
 .def_9197
))))))))))))

(push 1)

(assert
 (let ((.def_1560 (and tim.monitor_state.6__AT1 true)))
 (let ((.def_1561 (and tim.monitor_state.7__AT1 .def_1560)))
 (let ((.def_9198 (and .def_1561 true)))
 (let ((.def_9199 (and true .def_9198)))
 .def_9199
)))))

(check-sat)
(exit)
