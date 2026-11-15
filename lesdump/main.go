// Command lesdump parses a Les source file with the pinned upstream lexer/parser,
// runs the same type-inference pass as the upstream CLI, and prints a small,
// deterministic JSON AST. Only the node kinds listed in README.md are supported;
// anything else is an explicit error (exit status 2), never silently dropped.
package main

import (
	"encoding/json"
	"fmt"
	"os"
	"strings"

	"les/pkg/ast"
	"les/pkg/lexer"
	"les/pkg/parser"
	"les/pkg/types"
)

const schemaVersion = 1

type obj = map[string]any // encoding/json sorts map keys, so output is deterministic.

type unsupported struct {
	what string
	pos  ast.Position
}

func (u *unsupported) Error() string {
	return fmt.Sprintf("unsupported: %s at line %d col %d", u.what, u.pos.Line, u.pos.Col)
}

func pos(p ast.Position) obj { return obj{"line": p.Line, "col": p.Col} }

func node(kind string, p ast.Position, fields obj) obj {
	fields["kind"] = kind
	fields["pos"] = pos(p)
	return fields
}

func unsup(n ast.Node) error {
	return &unsupported{what: fmt.Sprintf("%T", n), pos: n.Pos()}
}

func stmts(list []ast.Stmt) ([]any, error) {
	out := make([]any, 0, len(list))
	for _, s := range list {
		v, err := stmt(s)
		if err != nil {
			return nil, err
		}
		out = append(out, v)
	}
	return out, nil
}

func stmt(s ast.Stmt) (obj, error) {
	switch n := s.(type) {
	case *ast.ExprStmt:
		e, err := expr(n.Value)
		if err != nil {
			return nil, err
		}
		return node("ExprStmt", n.Position, obj{"expr": e}), nil
	case *ast.VarDecl:
		e, err := expr(n.Value)
		if err != nil {
			return nil, err
		}
		return node("VarDecl", n.Position, obj{"name": n.Name, "type_annot": n.TypeAnnot, "value": e}), nil
	case *ast.FuncDef:
		if len(n.TypeParams) > 0 || n.BlockParam != nil {
			return nil, &unsupported{"FuncDef with type parameters or block parameter", n.Position}
		}
		params := make([]any, 0, len(n.Params))
		for _, p := range n.Params {
			if p.DefaultValue != nil || p.IsVariadic {
				return nil, &unsupported{"FuncDef parameter with default value or variadic", p.Position}
			}
			params = append(params, obj{"name": p.Name, "type_annot": p.TypeAnnot, "pos": pos(p.Position)})
		}
		body, err := stmts(n.Body)
		if err != nil {
			return nil, err
		}
		return node("FuncDef", n.Position, obj{"name": n.Name, "params": params, "return_type": n.ReturnType, "body": body}), nil
	}
	return nil, unsup(s)
}

func expr(e ast.Expr) (obj, error) {
	switch n := e.(type) {
	case *ast.Identifier:
		return node("Ident", n.Position, obj{"name": n.Name}), nil
	case *ast.IntLit:
		if n.BigValue != nil {
			return nil, &unsupported{"IntLit beyond int64", n.Position}
		}
		return node("Int", n.Position, obj{"value": n.Value}), nil
	case *ast.StringLit:
		return node("String", n.Position, obj{"value": n.Value}), nil
	case *ast.BinaryExpr:
		l, err := expr(n.Left)
		if err != nil {
			return nil, err
		}
		r, err := expr(n.Right)
		if err != nil {
			return nil, err
		}
		return node("Binary", n.Position, obj{"op": n.Op, "left": l, "right": r}), nil
	case *ast.ForceExpr:
		x, err := expr(n.Expr)
		if err != nil {
			return nil, err
		}
		return node("Force", n.Position, obj{"expr": x}), nil
	case *ast.CallExpr:
		if n.Block != nil {
			return nil, &unsupported{"CallExpr with trailing block", n.Position}
		}
		callee, err := expr(n.Callee)
		if err != nil {
			return nil, err
		}
		args := make([]any, 0, len(n.Args))
		for _, a := range n.Args {
			v, err := expr(a)
			if err != nil {
				return nil, err
			}
			args = append(args, v)
		}
		return node("Call", n.Position, obj{"callee": callee, "args": args}), nil
	}
	return nil, unsup(e)
}

func run(path string) (obj, int, error) {
	src, err := os.ReadFile(path)
	if err != nil {
		return nil, 2, err
	}
	l := lexer.NewLexer(string(src))
	p := parser.NewParser(l)
	p.SetFilename(path)
	prog := p.ParseProgram()
	if errs := p.Errors(); len(errs) > 0 {
		return nil, 2, fmt.Errorf("syntax error: %v", errs)
	}
	if prog.ModuleName != "" {
		return nil, 2, &unsupported{"module declaration", prog.Position}
	}
	body, err := stmts(prog.Body)
	if err != nil {
		return nil, 2, err
	}

	// Same type-inference pass as the upstream CLI (cmd/les/main.go), without a module loader:
	// import/module statements are unsupported above, so none can be reached.
	// The file path is replaced by "<FILE>" so that output does not depend on where the file lives.
	scrub := func(msg string) string { return strings.ReplaceAll(msg, path, "<FILE>") }
	analysis := obj{"status": "ok", "type_error": "", "type_warnings": []any{}}
	inf := types.NewInferencer()
	if err := inf.InferProgram(prog); err != nil {
		analysis["status"] = "type_error"
		analysis["type_error"] = scrub(fmt.Sprint(err))
	} else {
		warns := []any{}
		for _, w := range inf.Warnings() {
			warns = append(warns, scrub(fmt.Sprint(w)))
		}
		analysis["type_warnings"] = warns
	}
	return obj{"schema_version": schemaVersion, "kind": "Program", "analysis": analysis, "body": body}, 0, nil
}

func main() {
	if len(os.Args) != 2 {
		fmt.Fprintln(os.Stderr, "usage: lesdump FILE.les")
		os.Exit(2)
	}
	out, code, err := run(os.Args[1])
	if err != nil {
		fmt.Fprintln(os.Stderr, "lesdump:", err)
		os.Exit(code)
	}
	enc := json.NewEncoder(os.Stdout)
	enc.SetIndent("", "  ")
	enc.SetEscapeHTML(false)
	if err := enc.Encode(out); err != nil {
		fmt.Fprintln(os.Stderr, "lesdump:", err)
		os.Exit(2)
	}
}
