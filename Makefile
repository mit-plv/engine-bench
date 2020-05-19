.DEFAULT_GOAL := coq

COMPONENTS := coq
KINDS := perf pdf
ALL_COMPONENTS := $(COMPONENTS)

include Makefile.show

.PHONY: $(COMPONENTS)
$(COMPONENTS):
	$(HIDE)+$(MAKE) --no-print-directory -C $@

.PHONY: kinds
kinds::
	@ echo "Kinds: $(KINDS)"

.PHONY: targets
targets::
	@ echo "$(ALL_COMPONENTS)"

$(patsubst %,doc-build/%.pdf,$(COMPONENTS)) : doc-build/%.pdf :
	$(HIDE)mkdir -p doc-build
	$(HIDE)+$(MAKE) --no-print-directory -C $* copy-pdf OUTPUT=../$@

.PHONY: copy-pdf
copy-pdf: $(patsubst %,doc-build/%.pdf,$(COMPONENTS))

define add_kind
$(eval $(1)_COMPONENTS := $(addsuffix -$(1),$(COMPONENTS)))
$(eval ALL_COMPONENTS += $(1) $($(1)_COMPONENTS))

.PHONY: $(addsuffix -$(1),$(COMPONENTS))
$(addsuffix -$(1),$(COMPONENTS)) : %-$(1) :
	$$(HIDE)$$(MAKE) --no-print-directory -C $$* $(1)

.PHONY: $(1)
$(1): $(addsuffix -$(1),$(COMPONENTS))
endef

$(foreach kind,$(KINDS),$(eval $(call add_kind,$(kind))))

etc/tscfreq: etc/tscfreq.c
	$(CC) etc/tscfreq.c -s -Os -o etc/tscfreq
