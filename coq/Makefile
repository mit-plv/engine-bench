.DEFAULT_GOAL := coq

.PHONY: coq
coq:
	+$(MAKE) --no-print-directory -C PerformanceExperiments

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
