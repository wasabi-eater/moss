//! HIR (High-level Intermediate Representation) モジュール
//! 
//! このモジュールは、ASTからより構造化された中間表現への変換を担当します。
//! HIRは以下の主要な特徴を持ちます：
//! 
//! - 変数のスコープ管理
//! - 型推論のための準備
//! - 名前解決

mod core;
mod create_hir;

pub(crate) use core::*;
pub(crate) use create_hir::Maker; 