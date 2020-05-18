# KNOWNTARGETS will not be passed along to CoqMakefile
KNOWNTARGETS := update-_CoqProject clean cleanall foo
# KNOWNFILES will not get implicit targets from the final rule, and so
# depending on them won't invoke the submake
# Warning: These files get declared as PHONY, so any targets depending
# on them always get rebuilt
KNOWNFILES   := \
	Makefile \
	_CoqProject \
	Makefile.variables \
	Makefile.characters \
	Makefile.coq-versions \
	Makefile.timing

.DEFAULT_GOAL := all

include Makefile.characters
include Makefile.timing
include Makefile.coq-versions
include Makefile.variables

all:: invoke-coqmakefile
.PHONY: all

WARNINGS:=-notation-overridden

SORT_COQPROJECT = sed 's,[^/]*/,~&,g' | env LC_COLLATE=C sort | sed 's,~,,g' | uniq
.PHONY: update-_CoqProject
update-_CoqProject:
	$(SHOW)'ECHO > _CoqProject'
	$(HIDE)(echo '-R . $(PERF_LIB)'; echo '-arg -w -arg $(WARNINGS)'; (git ls-files "*.v" | $(SORT_COQPROJECT))) > _CoqProject

Makefile.coq: Makefile _CoqProject
	$(COQBIN)coq_makefile -f _CoqProject -o Makefile.coq

cleanall clean:: Makefile.coq
	$(MAKE) -f Makefile.coq $@
	rm -f Makefile.coq Makefile.coq.conf
.PHONY: cleanall clean

ifeq ($(MAKECMDGOALS),)
invoke-coqmakefile: Makefile.coq
	@$(MAKE) --no-print-directory -f Makefile.coq
else
ifneq ($(filter-out $(KNOWNFILES) $(KNOWNTARGETS),$(MAKECMDGOALS)),)
invoke-coqmakefile: Makefile.coq
	@$(MAKE) --no-print-directory -f Makefile.coq $(filter-out $(KNOWNFILES) $(KNOWNTARGETS),$(MAKECMDGOALS))
else
invoke-coqmakefile: Makefile.coq
	@true
endif
endif
.PHONY: invoke-coqmakefile

$(KNOWNFILES): ;

####################################################################
##                      Your targets here                         ##
####################################################################

# This should be the last rule, to handle any targets not declared above
%: invoke-coqmakefile
	@true
