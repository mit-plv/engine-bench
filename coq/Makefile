.DEFAULT_GOAL := coq

SUBFOLDERS := PerformanceExperiments PerformanceDemos
.PHONY: $(SUBFOLDERS)
$(SUBFOLDERS):
	+$(MAKE) -C $@

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
	+$(MAKE) --no-print-directory -C PerformanceExperiments perf-Sanity perf-SuperFast perf-Fast
	+$(MAKE) --no-print-directory -C PerformanceExperiments perf-csv

.PHONY: perf-lite
perf:
	+$(MAKE) --no-print-directory -C PerformanceExperiments perf-Sanity perf-SuperFast
	+$(MAKE) --no-print-directory -C PerformanceExperiments perf-csv

.PHONY: install-perf
install-perf:
	+$(MAKE) --no-print-directory -C PerformanceExperiments install-perf-Sanity install-perf-SuperFast install-perf-Fast

.PHONY: install-perf-lite
install-perf:
	+$(MAKE) --no-print-directory -C PerformanceExperiments install-perf-Sanity install-perf-SuperFast

.PHONY: install-perf-Sanity
install-perf-Sanity:
	+$(MAKE) --no-print-directory -C PerformanceExperiments install-perf-Sanity

.PHONY: pdf
pdf:
	+$(MAKE) --no-print-directory -C plots

.PHONY: copy-pdf
copy-pdf:
	cp plots/all.pdf $(OUTPUT)

.PHONY: doc
doc:
	+$(MAKE) --no-print-directory -C plots svg


.PHONY: copy-svg
copy-svg:
	cp -t $(OUTPUT) plots/*.svg

.PHONY: copy-perf
copy-perf:
	+$(MAKE) --no-print-directory -C PerformanceExperiments copy-perf OUTPUT="$(abspath $(OUTPUT))"

.PHONY: copy-doc
copy-doc: copy-svg copy-perf


include PerformanceExperiments/Makefile.variables
PERF_KINDS := $(addprefix perf-,$(SIZES))
.PHONY: $(PERF_KINDS)
$(PERF_KINDS):
	+$(MAKE) --no-print-directory -C PerformanceExperiments $@
