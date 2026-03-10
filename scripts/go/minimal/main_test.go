package main

import (
	"os"
	"path/filepath"
	"reflect"
	"testing"
)

func TestMinimalPathsTracksRemovedNodes(t *testing.T) {
	repoRoot := t.TempDir()
	writeTheory(t, repoRoot, "CSP-Prover-5-1-2020/CSP/Infra_common.thy", "Infra_common", []string{"Complex_Main"})
	writeTheory(t, repoRoot, "CSP-Prover-5-1-2020/CSP/Infra_nat.thy", "Infra_nat", []string{"Infra_common"})
	writeTheory(t, repoRoot, "CSP-Prover-5-1-2020/CSP/Infra_order.thy", "Infra_order", []string{"Infra_common"})
	writeTheory(t, repoRoot, "CSP-Prover-5-1-2020/CSP/Infra.thy", "Infra", []string{"Infra_nat", "Infra_order"})

	graph, err := (analyzer{theoryRootName: theoryRootName}).load(repoRoot)
	if err != nil {
		t.Fatalf("load graph: %v", err)
	}

	if got, want := graph.minimalPaths(nil), []string{
		"CSP-Prover-5-1-2020/CSP/Infra_common.thy",
	}; !reflect.DeepEqual(got, want) {
		t.Fatalf("minimal paths mismatch\n got: %v\nwant: %v", got, want)
	}

	removed := map[string]struct{}{
		normalizePath("./CSP-Prover-5-1-2020/CSP/Infra_common.thy"): {},
	}
	if got, want := graph.minimalPaths(removed), []string{
		"CSP-Prover-5-1-2020/CSP/Infra_nat.thy",
		"CSP-Prover-5-1-2020/CSP/Infra_order.thy",
	}; !reflect.DeepEqual(got, want) {
		t.Fatalf("minimal paths after removal mismatch\n got: %v\nwant: %v", got, want)
	}
}

func TestQualifiedImportsResolveToInternalTheory(t *testing.T) {
	repoRoot := t.TempDir()
	writeTheory(t, repoRoot, "CSP-Prover-5-1-2020/CSP/A.thy", "A", []string{"Complex_Main"})
	writeTheory(t, repoRoot, "CSP-Prover-5-1-2020/CSP/B.thy", "B", []string{"CSP.A", "HOL.Rings"})

	graph, err := (analyzer{theoryRootName: theoryRootName}).load(repoRoot)
	if err != nil {
		t.Fatalf("load graph: %v", err)
	}

	if got, want := graph.minimalPaths(nil), []string{
		"CSP-Prover-5-1-2020/CSP/A.thy",
	}; !reflect.DeepEqual(got, want) {
		t.Fatalf("minimal paths mismatch\n got: %v\nwant: %v", got, want)
	}

	removed := map[string]struct{}{
		normalizePath("CSP-Prover-5-1-2020/CSP/A.thy"): {},
		normalizePath("does/not/exist.thy"):            {},
	}
	if got, want := graph.minimalPaths(removed), []string{
		"CSP-Prover-5-1-2020/CSP/B.thy",
	}; !reflect.DeepEqual(got, want) {
		t.Fatalf("minimal paths after removal mismatch\n got: %v\nwant: %v", got, want)
	}
}

func TestBackupFilesAreIgnored(t *testing.T) {
	repoRoot := t.TempDir()
	writeTheory(t, repoRoot, "CSP-Prover-5-1-2020/DFP/DFP_DFtick.thy", "DFP_DFtick", []string{"Complex_Main"})
	writeTheory(t, repoRoot, "CSP-Prover-5-1-2020/DFP/DFP_DFtick_bak.thy", "DFP_DFtick", []string{"Complex_Main"})

	graph, err := (analyzer{theoryRootName: theoryRootName}).load(repoRoot)
	if err != nil {
		t.Fatalf("load graph: %v", err)
	}

	if got, want := graph.minimalPaths(nil), []string{
		"CSP-Prover-5-1-2020/DFP/DFP_DFtick.thy",
	}; !reflect.DeepEqual(got, want) {
		t.Fatalf("minimal paths mismatch\n got: %v\nwant: %v", got, want)
	}
}

func TestDuplicateTheoriesReturnError(t *testing.T) {
	repoRoot := t.TempDir()
	writeTheory(t, repoRoot, "CSP-Prover-5-1-2020/A/Foo.thy", "Foo", []string{"Complex_Main"})
	writeTheory(t, repoRoot, "CSP-Prover-5-1-2020/B/Foo.thy", "Foo", []string{"Complex_Main"})

	if _, err := (analyzer{theoryRootName: theoryRootName}).load(repoRoot); err == nil {
		t.Fatal("expected duplicate theory error")
	}
}

func TestParseImportsRejectsMissingBegin(t *testing.T) {
	_, err := parseImports("theory X\nimports A\n")
	if err == nil {
		t.Fatal("expected parse error")
	}
}

func writeTheory(t *testing.T, repoRoot, relativePath, theory string, imports []string) {
	t.Helper()

	absolutePath := filepath.Join(repoRoot, relativePath)
	if err := os.MkdirAll(filepath.Dir(absolutePath), 0o755); err != nil {
		t.Fatalf("mkdir %s: %v", absolutePath, err)
	}

	content := "theory " + theory + "\nimports"
	for _, imported := range imports {
		content += "\n  " + imported
	}
	content += "\nbegin\n"

	if err := os.WriteFile(absolutePath, []byte(content), 0o644); err != nil {
		t.Fatalf("write %s: %v", absolutePath, err)
	}
}
