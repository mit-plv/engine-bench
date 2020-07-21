.PHONY: all

all:
	/usr/bin/time -f "$@ (real: %e, user: %U, sys: %S, mem: %M ko)" leanpkg build

FILES = \
	src/rewrite_repeated_app.lean \
	src/rewrite_under_binders.lean \
	# end of list

profile: $(addsuffix .profile,$(FILES))
.PHONY: profile

$(addsuffix .profile,$(FILES)) : %.profile : %
	lean --profile $< 2>&1 | tee $@
