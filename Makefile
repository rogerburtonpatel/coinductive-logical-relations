KNOWNTARGETS := RocqMakefile
KNOWNFILES   := Makefile _RocqProject

.DEFAULT_GOAL := invoke-rocqmakefile

RocqMakefile: Makefile _RocqProject
	rocq makefile -f _RocqProject -o RocqMakefile

invoke-rocqmakefile: RocqMakefile
	$(MAKE) --no-print-directory -f RocqMakefile $(filter-out $(KNOWNTARGETS),$(MAKECMDGOALS))

.PHONY: invoke-rocqmakefile $(KNOWNFILES)

%: invoke-rocqmakefile
	@true
