package tree_sitter_poison_test

import (
	"testing"

	tree_sitter "github.com/tree-sitter/go-tree-sitter"
	tree_sitter_poison "github.com/jayc1323/poison-lang/bindings/go"
)

func TestCanLoadGrammar(t *testing.T) {
	language := tree_sitter.NewLanguage(tree_sitter_poison.Language())
	if language == nil {
		t.Errorf("Error loading Poison grammar")
	}
}
