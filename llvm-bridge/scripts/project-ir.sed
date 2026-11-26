# Project clang's -O1 emission of c/store8.c onto the textual surface
# LeanLLVM.Parser accepts (`ir/store8.ll`).  Every rule below removes or adds
# surface the model does not represent; none changes a modelled instruction.
#
# Parameter and function attributes: `noundef`, `zeroext`, `signext`,
# `nocapture`, `captures(none)`, `writeonly`.  They constrain values the model
# does not track (the ABI's extension of a narrow argument, pointer capture);
# `zeroext` on an `i8` argument does not change the byte's modelled value.
s/ noundef//g
s/ zeroext//g
s/ signext//g
s/ nocapture//g
s/ captures[(]none[)]//g
s/ writeonly//g
# Function-level surface the parser drops or refuses: `local_unnamed_addr` and
# the attribute-group reference `#0`.
s/ local_unnamed_addr//g
s/ #[0-9]+//g
# `nuw` on the getelementptr: a promise about the index arithmetic, not an
# instruction; dropping it widens the instruction the model proves things about.
s/ nuw//g
# Metadata attachments (the TBAA tag clang emits on the store).
s/, !tbaa ![0-9]+//g
# Clang numbers the first block only when it has a label; the parser's grammar
# requires one, and an unnamed first block is `entry` by LLVM's own convention.
/^define /a\
entry:
# Module-level lines the model has no field for: the raw source name, the target
# datalayout and triple, the attribute group, and the named metadata.
/^;/d
/^source_filename/d
/^target /d
/^attributes/d
/^!/d
# The blank lines clang leaves around its comment block and at end of file.
/^$/d
