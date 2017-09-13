package main

import (
	. "go/ast"
	"go/format"
	"go/importer"
	"go/token"
	"go/types"
	"log"
	"os"
)

type Tree struct {
	err   error
	pos   Node
	field *Field
	body  *BlockStmt
}

var (
	IdNeed                      = NewIdent("MISSING")
	IdZeta                      = NewIdent("z")
	IdBinary                    = NewIdent("binary")
	IdRead, IdWrite             = NewIdent("Read"), NewIdent("Write")
	IdReadBinary, IdWriteBinary = NewIdent("ReadBinary"), NewIdent("WriteBinary")
	IdR, IdW                    = NewIdent("r"), NewIdent("w")

	IdBinaryDotRead  = &SelectorExpr{X: IdBinary, Sel: IdRead}
	IdBinaryDotWrite = &SelectorExpr{X: IdBinary, Sel: IdWrite}

	SelZRead        = &SelectorExpr{X: IdZeta, Sel: IdRead}
	SelZWrite       = &SelectorExpr{X: IdZeta, Sel: IdWrite}
	SelZReadBinary  = &SelectorExpr{X: IdZeta, Sel: IdReadBinary}
	SelZWriteBinary = &SelectorExpr{X: IdZeta, Sel: IdWriteBinary}
)

type Func func(*SelectorExpr, Expr, *SelectorExpr) Func

func Z(field Expr) Expr {
	switch t := field.(type) {
	case *Ident:
		return &SelectorExpr{
			X:   IdZeta,
			Sel: t,
		}
	}
	return field
}

func Read1(field Expr) Stmt { return IOFunc1(&SelectorExpr{X: IdBinary, Sel: IdRead}, IdW, Z(field)) }
func Read2(field Expr) Stmt { return IOFunc2(SelZRead, IdR, Z(field)) }
func Read3(field Expr) Stmt { return IOFunc3(SelZReadBinary, IdR, Z(field)) }
func Read4(field Expr) Stmt { return IOFunc4(SelZRead, IdR, Z(field)) }

func Write1(field Expr) Stmt { return IOFunc1(IdBinaryDotWrite, IdW, Z(field)) }
func Write2(field Expr) Stmt { return IOFunc2(IdWrite, IdW, Z(field)) }
func Write3(field Expr) Stmt { return IOFunc3(IdWriteBinary, IdW, Z(field)) }
func Write4(field Expr) Stmt { return IOFunc4(IdWrite, IdW, Z(field)) }

//var Wired = NewInterface(methods []*Func, embeddeds []*Named)
type IOFunc func(Expr) Stmt

func main() {
	astWireTypes()
}

func ReadBinary() {

}

// Method creates the WriteBinary and ReadBinary method for struct S
//
//
func Method(t *TypeSpec) (funs []*FuncDecl) {
	N := t.Name
	S := t.Type.(*StructType)

	for _, m := range []struct {
		n, i, r  string
		resolver func(f *Field) Stmt
	}{
		{"WriteBinary", "Writer", "w", func(f *Field) Stmt { _, w := ResolveFieldFunc(f); return w }},
		{"ReadBinary", "Reader", "r", func(f *Field) Stmt { r, _ := ResolveFieldFunc(f); return r }},
	} {
		f := &FuncDecl{
			Name: &Ident{Name: m.n, Obj: &Object{Kind: Fun, Name: m.n}},
			Recv: &FieldList{List: []*Field{
				{
					Names: []*Ident{{Name: "z", Obj: &Object{Kind: Var, Name: "z"}}},
					Type:  N,
				},
			}},
			Type: &FuncType{
				Params: &FieldList{
					List: []*Field{
						{
							Names: []*Ident{{Name: m.r, Obj: &Object{Kind: Var, Name: m.r}}},
							Type: &SelectorExpr{
								X:   &Ident{Name: "io"},
								Sel: &Ident{Name: m.i},
							},
						},
					},
				},
				Results: &FieldList{List: []*Field{{Type: &Ident{Name: "error"}}}},
			},
			Body: &BlockStmt{List: []Stmt{}},
		}

		for _, v := range S.Fields.List {
			// Ascertain something about the Field, then determine which version of Write to use
			// for that field
			f.Body.List = append(f.Body.List, m.resolver(v))
		}
		f.Body.List = append(f.Body.List, &ReturnStmt{Results: []Expr{&Ident{Name: "nil"}}})
		funs = append(funs, f)
	}

	return funs
}

func IOLoop(body Stmt, n Expr) Stmt {
	return &BlockStmt{
		List: []Stmt{
			&ForStmt{
				Init: &AssignStmt{
					Lhs: []Expr{&Ident{Name: "i"}},
					Tok: token.DEFINE,
					Rhs: []Expr{&BasicLit{Kind: token.INT, Value: "0"}},
				},
				Cond: &BinaryExpr{
					X:  &Ident{Name: "i"},
					Op: token.LSS,
					Y:  n,
				},
				Post: &IncDecStmt{
					Tok: token.INC,
					X:   &Ident{Name: "i"},
				},
				Body: &BlockStmt{
					List: []Stmt{body},
				},
			},
		},
	}
}

// ResolveFieldFunc computes the correct read and write
// methods for the field type of a struct.
func ResolveFieldFunc(f *Field) (r, w Stmt) {
	return Resolve(f.Names[0], f.Type)
}

func Resolve(n Expr, t Expr) (r, w Stmt) {
	if t == nil {
		return nil, nil
	}
	// TODO:
	// check if the type implements wire9.Wire
	// if types.Implements

	switch t := t.(type) {
	case *ArrayType:
		// peek
		if k, ok := t.Elt.(*Ident); ok {
			if k.Name == "byte" {
				r := IOFunc2(IdRead, IdR, n)
				w := IOFunc2(IdWrite, IdW, n)
				return r, w
			}
		}
		x := &BasicLit{Kind: token.INT, Value: "10"}
		r, w := Resolve(
			&IndexExpr{
				X:     Z(n),
				Index: NewIdent("i"),
			},
			t.Elt,
		)
		return IOLoop(r, x), IOLoop(w, x)
	case *FuncType:
		// compare signature to wirefunc
	case *InterfaceType:
		panic("interface not supported")
	case *StarExpr:
		return Resolve(n, t.X)
	case *ChanType:
		panic("chan not supported")
	case *MapType:
		panic("map not supported")
	case *Ident:
		return Read1(n), Write1(n)
	}
	panic("Resolve unreachable")
}

type X struct {
	fileroot *File
	list     []*FuncDecl
}

func (x *X) Visit(node Node) (w Visitor) {
	if node == nil {
		return nil
	}
	switch t := node.(type) {
	case *File:
		x.fileroot = t
		for _, v := range t.Decls {
			x.Visit(v)
		}
	case *GenDecl:
		if t.Tok == token.TYPE {
			for _, v := range t.Specs {
				x.Visit(v)
			}
		}
	case *TypeSpec:
		if _, ok := t.Type.(*StructType); ok {
			for _, v := range Method(t) {
				x.fileroot.Decls = append(x.fileroot.Decls, v)
			}
		}
	}
	return nil
}
func astWireTypes() {
	x := &File{
		Name: &Ident{Name: "main"},
		Decls: []Decl{
			&GenDecl{
				Tok: token.IMPORT,
				Specs: []Spec{
					&ImportSpec{Path: &BasicLit{Kind: token.STRING, Value: "\"fmt\""}},
				},
			},
			&GenDecl{
				Tok: token.IMPORT,
				Specs: []Spec{
					&ImportSpec{Path: &BasicLit{Kind: token.STRING, Value: "\"io\""}},
				},
			},
			&GenDecl{
				Tok: token.IMPORT,
				Specs: []Spec{
					&ImportSpec{Path: &BasicLit{Kind: token.STRING, Value: "\"encoding/binary\""}},
				},
			},
			&GenDecl{
				Tok: token.TYPE,
				Specs: []Spec{
					&TypeSpec{
						Name: &Ident{
							Name: "Some",
							Obj: &Object{
								Kind: Typ,
								Name: "Some",
							},
						},
						Type: &StructType{
							Fields: &FieldList{
								List: []*Field{{
									Names: []*Ident{{Name: "n", Obj: &Object{Kind: Var, Name: "n"}}},
									Type:  &Ident{Name: "int"},
								}, {
									Names: []*Ident{{Name: "name", Obj: &Object{Kind: Var, Name: "name"}}},
									Type:  &ArrayType{Elt: &Ident{Name: "byte"}},
								}, {
									Names: []*Ident{{Name: "str", Obj: &Object{Kind: Var, Name: "str"}}},
									Type:  &ArrayType{Elt: &Ident{Name: "int"}},
								}},
							},
							Incomplete: false,
						},
					},
				},
			},
		},
	}

	v := new(X)
	Walk(v, x)

	fset := token.NewFileSet()
	fset.AddFile("/usr/as/wire9/cmd/synth.go", 1, 2935)
	format.Node(os.Stdout, fset, x)
	conf := &types.Config{Importer: importer.Default()}
	info := &types.Info{
		Types:      make(map[Expr]types.TypeAndValue),
		Defs:       make(map[*Ident]types.Object),
		Uses:       make(map[*Ident]types.Object),
		Implicits:  make(map[Node]types.Object),
		Selections: make(map[*SelectorExpr]*types.Selection),
		Scopes:     make(map[Node]*types.Scope),
	}
	pkg, err := conf.Check("main", fset, []*File{x}, info)
	if err != nil {
		log.Fatal(err)
	}
	pkg = pkg

}

// IOFunc1 creates a call to binary IO function with three arguments and one return. The return result
// is an error. The fn parameter indicates "Read" or "Write" through an Ident, pipe and field provide
// the writer/reader and the structfield to fill in.
//
// func binary.Read(io.Reader, binary.LittleEndian, field) (err error)
//
func IOFunc1(fn, pipe, field Expr) Stmt {
	return &IfStmt{
		Init: &AssignStmt{
			Lhs: []Expr{&Ident{Name: "err"}},
			Tok: token.DEFINE,
			Rhs: []Expr{&CallExpr{
				Fun: fn,
				Args: []Expr{
					pipe,
					&SelectorExpr{
						X:   &Ident{Name: "binary"},
						Sel: &Ident{Name: "LittleEndian"},
					},
					field,
				},
			}},
		},
		Cond: &BinaryExpr{
			X:  &Ident{Name: "err"},
			Op: token.NEQ,
			Y:  &Ident{Name: "nil"},
		},
		Body: &BlockStmt{
			List: []Stmt{&ReturnStmt{Results: []Expr{&Ident{Name: "err"}}}},
		},
	}
}

// IOFunc2 creates a Read/Write call:
// func r.Read(p []byte) (n int, err error)
//
func IOFunc2(fn, pipe, data Expr) Stmt {
	return &IfStmt{
		Init: &AssignStmt{
			Lhs: []Expr{&Ident{Name: "n"}, &Ident{Name: "err"}},
			Tok: token.DEFINE,
			Rhs: []Expr{&CallExpr{
				Fun: &SelectorExpr{
					X:   pipe,
					Sel: fn.(*Ident),
				},
				Args: []Expr{
					&SelectorExpr{
						X:   &Ident{Name: "z"},
						Sel: data.(*Ident),
					},
				},
			}},
		},
		Cond: &BinaryExpr{
			X:  &Ident{Name: "err"},
			Op: token.NEQ,
			Y:  &Ident{Name: "nil"},
		},
		Body: &BlockStmt{
			List: []Stmt{&ReturnStmt{Results: []Expr{&Ident{Name: "err"}}}},
		},
	}
}

// IOFunc3 creates a call to an underlying ReadBinary or WriteBinary
// z.field.ReadBinary(w io.Writer)
//
func IOFunc3(fn, pipe, field Expr) Stmt {
	return &IfStmt{
		Init: &AssignStmt{
			Lhs: []Expr{&Ident{Name: "err"}},
			Tok: token.DEFINE,
			Rhs: []Expr{&CallExpr{
				Fun: &SelectorExpr{
					X:   &SelectorExpr{X: &Ident{Name: "z"}, Sel: field.(*Ident)},
					Sel: fn.(*Ident),
				},
				Args: []Expr{pipe},
			},
			},
		},
		Cond: &BinaryExpr{
			X:  &Ident{Name: "err"},
			Op: token.NEQ,
			Y:  &Ident{Name: "nil"},
		},
		Body: &BlockStmt{
			List: []Stmt{&ReturnStmt{Results: []Expr{&Ident{Name: "err"}}}},
		},
	}
}

// IOFunc4 create a block that assigns field to the result of processing
// the dependent variable through fn. It then executes IOFunc3 on the
// assigned field.
//
func IOFunc4(fn, pipe, field Expr) Stmt {
	return &BlockStmt{
		List: []Stmt{
			&AssignStmt{
				Lhs: []Expr{&SelectorExpr{
					X:   &Ident{Name: "z"},
					Sel: field.(*Ident),
				}, &Ident{Name: "err"}},
				Tok: token.ASSIGN,
				Rhs: []Expr{&CallExpr{
					Fun:  fn,
					Args: []Expr{field},
				}},
			},
			&IfStmt{
				Cond: &BinaryExpr{
					X:  &Ident{Name: "err"},
					Op: token.NEQ,
					Y:  &Ident{Name: "nil"},
				},
				Body: &BlockStmt{
					List: []Stmt{&ReturnStmt{Results: []Expr{&Ident{Name: "err"}}}},
				},
			},
			&IfStmt{
				Init: &AssignStmt{
					Lhs: []Expr{&Ident{Name: "err"}},
					Tok: token.DEFINE,
					Rhs: []Expr{&CallExpr{
						Fun: &SelectorExpr{
							X:   &SelectorExpr{X: &Ident{Name: "z"}, Sel: field.(*Ident)},
							Sel: fn.(*Ident),
						},
						Args: []Expr{pipe},
					},
					},
				},
				Cond: &BinaryExpr{
					X:  &Ident{Name: "err"},
					Op: token.NEQ,
					Y:  &Ident{Name: "nil"},
				},
				Body: &BlockStmt{
					List: []Stmt{&ReturnStmt{Results: []Expr{&Ident{Name: "err"}}}},
				},
			},
		},
	}
}

// Field needs to be an expression
