.DEFAULT_GOAL := coq

COMPONENTS := coq

.PHONY: $(COMPONENTS)
$(COMPONENTS):
	$(MAKE) --no-print-directory -C $@
