use serde::Serialize;

#[derive(Default, Serialize)]
pub struct DebugSymbol {
    pub globals: Vec<SymbolDef>,
    pub labels: Vec<SymbolDef>,
}

#[derive(Serialize)]
pub struct SymbolDef {
    pub label: String,
    pub addr: u32,
}
