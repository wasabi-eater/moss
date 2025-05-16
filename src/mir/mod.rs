//! MIR (Middle Intermediate Representation) モジュール
//! 
//! このモジュールは、高レベルな中間表現（HIR）からより低レベルな表現への変換を担当します。
//! MIRは以下の主要な特徴を持ちます：
//! 
//! - メモリ操作（Move、Copy、Drop）の明示的な表現
//! - 制御フローの単純化
//! - 型情報の保持
//! - 最適化のためのユーティリティ

mod core;
mod create_mir;

pub(crate) use core::*;
pub(crate) use create_mir::Maker; 