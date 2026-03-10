package main

import (
	"bufio"
	"errors"
	"fmt"
	"io"
	"io/fs"
	"os"
	"path/filepath"
	"sort"
	"strings"
)

const theoryRootName = "CSP-Prover-5-1-2020"

type analyzer struct {
	theoryRootName string
}

type theoryGraph struct {
	deps map[string][]string
}

func main() {
	if err := run(os.Stdin, os.Stdout, os.Stderr); err != nil {
		fmt.Fprintln(os.Stderr, err)
		os.Exit(1)
	}
}

func run(stdin io.Reader, stdout, stderr io.Writer) error {
	removed, err := readRemovedPaths(stdin)
	if err != nil {
		return err
	}

	graph, err := (analyzer{theoryRootName: theoryRootName}).load(".")
	if err != nil {
		return err
	}

	minimal := graph.minimalPaths(removed)
	for _, path := range minimal {
		if _, err := fmt.Fprintln(stdout, "./"+path); err != nil {
			return err
		}
	}

	return nil
}

func readRemovedPaths(r io.Reader) (map[string]struct{}, error) {
	removed := make(map[string]struct{})
	scanner := bufio.NewScanner(r)
	for scanner.Scan() {
		path := normalizePath(scanner.Text())
		if path == "" {
			continue
		}
		removed[path] = struct{}{}
	}
	if err := scanner.Err(); err != nil {
		return nil, fmt.Errorf("read stdin: %w", err)
	}
	return removed, nil
}

func (a analyzer) load(repoRoot string) (*theoryGraph, error) {
	theoryRoot := filepath.Join(repoRoot, a.theoryRootName)
	theoryFiles, err := collectTheoryFiles(repoRoot, theoryRoot, a.theoryRootName)
	if err != nil {
		return nil, err
	}

	byTheory := make(map[string]string, len(theoryFiles))
	for _, theoryFile := range theoryFiles {
		if existing, exists := byTheory[theoryFile.theory]; exists {
			return nil, fmt.Errorf("duplicate theory %q: %s and %s", theoryFile.theory, existing, theoryFile.path)
		}
		byTheory[theoryFile.theory] = theoryFile.path
	}

	deps := make(map[string][]string, len(theoryFiles))
	for _, theoryFile := range theoryFiles {
		deps[theoryFile.path] = nil
		seen := make(map[string]struct{})
		for _, imported := range theoryFile.imports {
			theoryName := imported
			if lastDot := strings.LastIndex(imported, "."); lastDot >= 0 {
				theoryName = imported[lastDot+1:]
			}
			depPath, ok := byTheory[theoryName]
			if !ok {
				continue
			}
			if _, exists := seen[depPath]; exists {
				continue
			}
			seen[depPath] = struct{}{}
			deps[theoryFile.path] = append(deps[theoryFile.path], depPath)
		}
		sort.Strings(deps[theoryFile.path])
	}

	return &theoryGraph{deps: deps}, nil
}

type theoryFile struct {
	path    string
	theory  string
	imports []string
}

func collectTheoryFiles(repoRoot, theoryRoot, theoryRootName string) ([]theoryFile, error) {
	var theoryFiles []theoryFile
	err := filepath.WalkDir(theoryRoot, func(path string, d fs.DirEntry, err error) error {
		if err != nil {
			return err
		}
		if d.IsDir() {
			return nil
		}
		if filepath.Ext(path) != ".thy" || strings.HasSuffix(path, "_bak.thy") {
			return nil
		}

		contents, err := os.ReadFile(path)
		if err != nil {
			return fmt.Errorf("read %s: %w", path, err)
		}

		theory, err := parseTheoryName(string(contents))
		if err != nil {
			return fmt.Errorf("%s: %w", path, err)
		}

		imports, err := parseImports(string(contents))
		if err != nil {
			return fmt.Errorf("%s: %w", path, err)
		}

		relativePath, err := filepath.Rel(repoRoot, path)
		if err != nil {
			return fmt.Errorf("relativize %s: %w", path, err)
		}

		theoryFiles = append(theoryFiles, theoryFile{
			path:    normalizePath(relativePath),
			theory:  theory,
			imports: imports,
		})
		return nil
	})
	if err != nil {
		if errors.Is(err, fs.ErrNotExist) {
			return nil, fmt.Errorf("theory root %q does not exist", theoryRootName)
		}
		return nil, err
	}

	sort.Slice(theoryFiles, func(i, j int) bool {
		return theoryFiles[i].path < theoryFiles[j].path
	})
	return theoryFiles, nil
}

func parseTheoryName(contents string) (string, error) {
	scanner := bufio.NewScanner(strings.NewReader(contents))
	for scanner.Scan() {
		line := strings.TrimSpace(scanner.Text())
		if !strings.HasPrefix(line, "theory ") {
			continue
		}
		fields := strings.Fields(line)
		if len(fields) < 2 {
			return "", errors.New("malformed theory declaration")
		}
		return fields[1], nil
	}
	if err := scanner.Err(); err != nil {
		return "", fmt.Errorf("scan theory declaration: %w", err)
	}
	return "", errors.New("missing theory declaration")
}

func parseImports(contents string) ([]string, error) {
	scanner := bufio.NewScanner(strings.NewReader(contents))
	inImports := false
	var imports []string

	for scanner.Scan() {
		line := strings.TrimSpace(scanner.Text())
		switch {
		case !inImports && line == "imports":
			inImports = true
		case !inImports && strings.HasPrefix(line, "imports "):
			inImports = true
			imports = appendImports(imports, strings.TrimSpace(strings.TrimPrefix(line, "imports")))
		case inImports && strings.HasPrefix(line, "begin"):
			return imports, nil
		case inImports:
			imports = appendImports(imports, line)
		}
	}

	if err := scanner.Err(); err != nil {
		return nil, fmt.Errorf("scan imports block: %w", err)
	}
	if !inImports {
		return nil, errors.New("missing imports block")
	}
	return nil, errors.New("missing begin after imports block")
}

func appendImports(imports []string, line string) []string {
	if line == "" {
		return imports
	}

	for _, field := range strings.Fields(line) {
		if field == "(" || strings.HasPrefix(field, "(") {
			break
		}
		imports = append(imports, field)
	}
	return imports
}

func (g *theoryGraph) minimalPaths(removed map[string]struct{}) []string {
	var minimal []string
	for path, deps := range g.deps {
		if _, isRemoved := removed[path]; isRemoved {
			continue
		}

		hasRemainingDeps := false
		for _, dep := range deps {
			if _, isRemoved := removed[dep]; isRemoved {
				continue
			}
			hasRemainingDeps = true
			break
		}
		if !hasRemainingDeps {
			minimal = append(minimal, path)
		}
	}

	sort.Strings(minimal)
	return minimal
}

func normalizePath(path string) string {
	path = strings.TrimSpace(path)
	if path == "" {
		return ""
	}
	path = filepath.ToSlash(filepath.Clean(path))
	path = strings.TrimPrefix(path, "./")
	if path == "." {
		return ""
	}
	return path
}
