use ir_asm_ast_isa1st::*;
use ir_asm_virtual_ast_isa1st::Prog;

pub fn exe_transform<Ident, Label>(
    Prog {
        float_map,
        globals_map,
        fundefs,
        entry_point,
    }: Prog<Ident, Label, TextSegment<Label>>,
) -> Asm<Ident, Label> {
    use DataSegmentElem::*;
    let mut text_segment = Vec::new();
    for f in fundefs {
        text_segment.extend(f.into_inner().into_iter());
    }
    Asm {
        data_segment: DataSegment::with_globals(
            globals_map,
            float_map
                .into_iter()
                .flat_map(|(data, (label, _))| {
                    [
                        Directive(DataSegmentDirective::Labeled(label)),
                        Data(DataKind::Long(data)),
                    ]
                })
                .collect(),
        ),
        text_segment: TextSegment::new(text_segment),
        entry_point,
    }
}
