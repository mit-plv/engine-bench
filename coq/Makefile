.DEFAULT_GOAL := coq

SUBFOLDERS := PerformanceExperiments PerformanceDemos
.PHONY: $(SUBFOLDERS)
$(SUBFOLDERS):
	+$(MAKE) --no-print-directory -C $@

SUBFOLDERS_INSTALL := $(addsuffix -install,$(SUBFOLDERS))
.PHONY: $(SUBFOLDERS_INSTALL)
$(SUBFOLDERS_INSTALL) : %-install :
	+$(MAKE) --no-print-directory -C $* install

.PHONY: coq
coq: $(SUBFOLDERS)

.PHONY: install
install: $(SUBFOLDERS_INSTALL)

.PHONY: perf
perf:
	+$(MAKE) --no-print-directory -C PerformanceExperiments perf-SuperFast perf-Fast
	+$(MAKE) --no-print-directory -C PerformanceExperiments perf-csv

.PHONY: pdf
pdf:
	+$(MAKE) --no-print-directory -C plots

.PHONY: copy-pdf
copy-pdf:
	cp plots/all.pdf $(OUTPUT)
