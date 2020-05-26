.DEFAULT_GOAL := all

COMPONENTS := coq
KINDS := perf pdf doc install install-perf perf-Sanity install-perf-Sanity
ALL_COMPONENTS := $(COMPONENTS)

include Makefile.show

.PHONY: all
all: coq

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

$(patsubst %,doc-build/%,$(COMPONENTS)) : doc-build/% :
	$(HIDE)mkdir -p $@
	$(HIDE)+$(MAKE) --no-print-directory -C $* copy-doc OUTPUT=../$@

.PHONY: copy-doc
copy-doc: $(patsubst %,doc-build/%,$(COMPONENTS))

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

.PHONY: test-README-links
all: test-README-links
GET_README_LINKS:=grep -o '\[[^]]*\](\./[^)]*)' README.md | sed 's/\[[^]]*]//g; s/^(//g; s/)$$//g' | sort | uniq
README_FILES:=$(shell $(GET_README_LINKS))
BAD_README_LINKS:=$(filter-out $(wildcard $(README_FILES)),$(README_FILES))
ifneq ($(BAD_README_LINKS),)
test-README-links:
	@echo 'ERROR: The following files do not exist: $(BAD_README_LINKS)'
	@false
else
test-README-links: ;
endif

etc/tscfreq: etc/tscfreq.c
	$(CC) etc/tscfreq.c -s -Os -o etc/tscfreq
