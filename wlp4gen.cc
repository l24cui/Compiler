#include <iostream>
#include <map>
#include <sstream>
#include <string>
#include <utility>
#include <list>
#include <stack>
using namespace std;

struct Tree {
    pair<string,string> node;
    list<Tree> children;

    Tree() {}
    Tree(pair<string,string> n):node{n} {}
};

//symbol table (functionName,(variableName,(type,frameStackOffset)))
map<string,map<string,pair<string,int>>> symtab;
//(functionName,(variableName))
list<pair<string,list<string>>> symtabOrder;
//(function,numOfDclSigniature)
map<string,int> signatures;
//a parse tree to store the input (the tree representing the wlp4i file)
Tree parse;
//stack of names of called procedures
stack<string> procCalls;

string funcname = "";
string varname = "";
string type = "";
string callproc = "";
int offset = 0;
int ifcount = 0;
int loopcount = 0;
int delcount = 0;
list<pair<string,list<string>>>::iterator argprocit;
list<string>::iterator argit;

bool isterm(string& s);
Tree& childrenAt(Tree& t,int n);
bool goodtype(Tree& t);
string findtype(Tree& t);
void insert(Tree& t);
void push(int reg);
void pop(int reg);
void proceduresCode(Tree& t);
void procedureCode(Tree& t);
void mainCode(Tree& t);
void dclsCode(Tree& t);
void stmtsCode(Tree& t);
void stmtCode(Tree& t);
void lvalCode(Tree& t);
void factCode(Tree& t);
void argspushCode(Tree& t);
void testCode(Tree& t);
void exprCode(Tree& t);
void termCode(Tree& t);


//Check if string is a terminal
bool isterm(string& s) {
  return ((s == "ID") || (s == "NUM") || (s == "LPAREN") || (s == "RPAREN") ||
          (s == "LBRACE") || (s == "RBRACE") || (s == "RETURN") || (s == "IF") ||
          (s == "ELSE") || (s == "WHILE") || (s == "PRINTLN") || (s == "WAIN") ||
          (s == "BECOMES") || (s == "INT") || (s == "EQ") || (s == "NE") || (s == "LT") ||
          (s == "GT") || (s == "LE") || (s == "GE") || (s == "PLUS") || (s == "MINUS") ||
          (s == "STAR") || (s == "SLASH") || (s == "PCT") || (s == "COMMA") ||
          (s == "SEMI") || (s == "NEW") || (s == "DELETE") || (s == "LBRACK") ||
          (s == "RBRACK") || (s == "AMP") || (s == "NULL") || (s == "BOF") || (s == "EOF"));
}

Tree& childrenAt(Tree& t,int n) {
  list<Tree>::iterator it = t.children.begin();
  for (int i = 0; i != n; ++i) {
    ++it;
  }
  return *it;
}

bool goodtype(Tree& t) {
  bool good = true;
  if (t.node.second == "") {
    good = true;
  } else if (t.node.first == "test") {
    string expr1type = findtype(childrenAt(t,0));
    string expr2type = findtype(childrenAt(t,2));
    if (expr1type != expr2type) {
      good = false;
    }
  } else if (t.node.second == "WHILE LPAREN test RPAREN LBRACE statements RBRACE") {
    good = goodtype(childrenAt(t,2)) && goodtype(childrenAt(t,5));
  } else if (t.node.second == "IF LPAREN test RPAREN LBRACE statements RBRACE ELSE LBRACE statements RBRACE") {
    good = goodtype(childrenAt(t,2)) && goodtype(childrenAt(t,5)) && goodtype(childrenAt(t,9));
  } else if (t.node.second == "DELETE LBRACK RBRACK expr SEMI") {
    if (findtype(childrenAt(t,3)) != "int*") {
      good = false;
    }
  } else if (t.node.second == "PRINTLN LPAREN expr RPAREN SEMI") {
    if (findtype(childrenAt(t,2)) != "int") {
      good = false;
    }
  } else if (t.node.second == "lvalue BECOMES expr SEMI") {
    string lvaltype = findtype(childrenAt(t,0));
    if (findtype(childrenAt(t,2)) != lvaltype) {
      good = false;
    }
  } else if ((t.node.second == "statements statement") || (t.node.second == "procedure procedures")) {
    good = goodtype(childrenAt(t,0)) && goodtype(childrenAt(t,1));
  } else if ((t.node.second == "dcls dcl BECOMES NUM SEMI") || (t.node.second == "dcls dcl BECOMES NULL SEMI")) {
    string dcltype;
    if (childrenAt(t,1).children.front().node.second == "INT") {
      dcltype = "int";
    } else if (childrenAt(t,1).children.front().node.second == "INT STAR") {
      dcltype = "int*";
    }
    good = goodtype(childrenAt(t,0)) &&
           (((t.node.second == "dcls dcl BECOMES NUM SEMI") && (dcltype == "int")) ||
            ((t.node.second == "dcls dcl BECOMES NULL SEMI") && (dcltype == "int*")));
  } else if (t.node.second == "main") {
    good = goodtype(childrenAt(t,0));
  } else if (t.node.second == "INT ID LPAREN params RPAREN LBRACE dcls statements RETURN expr SEMI RBRACE") {
    funcname = childrenAt(t,1).node.second;
    good = goodtype(childrenAt(t,6)) && goodtype(childrenAt(t,7)) && (findtype(childrenAt(t,9)) == "int");
  } else if (t.node.second == "INT WAIN LPAREN dcl COMMA dcl RPAREN LBRACE dcls statements RETURN expr SEMI RBRACE") {
    funcname = "wain";
    string dcltype;
    if (childrenAt(t,5).children.front().node.second == "INT") {
      dcltype = "int";
    } else if (childrenAt(t,5).children.front().node.second == "INT STAR") {
      dcltype = "int*";
    }
    good = goodtype(childrenAt(t,8)) && (dcltype == "int") && goodtype(childrenAt(t,9)) && (findtype(childrenAt(t,11)) == "int");
  } else if ((t.node.second == "LPAREN expr RPAREN") || (t.node.second == "LPAREN lvalue RPAREN")) {
    good = goodtype(childrenAt(t,1));
  } else if (t.node.second == "AMP lvalue") {
    good = (findtype(childrenAt(t,1)) == "int");
  } else if (t.node.second == "STAR factor") {
    good = (findtype(childrenAt(t,1)) == "int*");
  } else if (t.node.second == "NEW INT LBRACK expr RBRACK") {
    good = (findtype(childrenAt(t,3)) == "int");
  } else if (t.node.second == "ID LPAREN RPAREN") {
    string id = childrenAt(t,0).node.second;
    good = ((signatures.count(id)) && (signatures.at(id) == 0));
  } else if (t.node.second == "ID LPAREN arglist RPAREN") {
    callproc = childrenAt(t,0).node.second;
    argprocit = symtabOrder.begin();
    for (;argprocit != symtabOrder.end();++argprocit) {
      if (argprocit->first == callproc) break;
    }
    argit = (argprocit->second).begin();
    good = (argprocit != symtabOrder.end()) && (goodtype(childrenAt(t,2)));
  } else if (t.node.first == "arglist") {
    if ((!(symtab.count(callproc))) || (!(symtab.at(callproc).count(*argit)))) throw string ("ERROR");
    string argtype = symtab.at(callproc).at(*argit).first;
    good = (findtype(childrenAt(t,0)) == argtype);
    ++argit;
    if (t.node.first == "expr COMMA arglist") {
      good = (good && goodtype(childrenAt(t,2)));
    }
  } else if (t.node.first == "start") {
    good = goodtype(childrenAt(t,1));
  }
  return good;
}

string findtype(Tree& t) {
  if (t.node.first == "expr") {
    if (t.node.second == "term") {
      return findtype(t.children.front());
    } else if (t.node.second == "expr PLUS term") {
      string exprtype = findtype(childrenAt(t,0));
      string termtype = findtype(childrenAt(t,2));
      if ((exprtype == "int") && (termtype == "int")) {
        return "int";
      } else if ((exprtype == "int*") && (termtype == "int")) {
        return "int*";
      } else if ((exprtype == "int") && (termtype == "int*")) {
        return "int*";
      } else throw string("ERROR");
    } else {
      string exprtype = findtype(childrenAt(t,0));
      string termtype = findtype(childrenAt(t,2));
      if ((exprtype == "int") && (termtype == "int")) {
        return "int";
      } else if ((exprtype == "int*") && (termtype == "int")) {
        return "int*";
      } else if ((exprtype == "int*") && (termtype == "int*")) {
        return "int";
      } else throw string("ERROR");
    }
  } else if (t.node.first == "term") {
    if (t.node.second == "factor") {
      return findtype(t.children.front());
    } else {
      string termtype = findtype(childrenAt(t,0));
      string factype = findtype(childrenAt(t,2));
      if ((termtype == "int") && (factype == "int")) {
        return "int";
      } else throw string("ERROR");
    }
  } else if (t.node.first == "lvalue") {
    if (t.node.second == "ID") {
      if (!(symtab.count(funcname))) throw string("ERROR");
      if (!(symtab.at(funcname).count(t.children.front().node.second))) throw string("ERROR");
      return symtab.at(funcname).at(t.children.front().node.second).first;
    } else if (t.node.second == "STAR factor") {
      if (findtype(childrenAt(t,1)) == "int*") {
        return "int";
      } else throw string("ERROR");
    } else {
      return findtype(childrenAt(t,1));
    }
  } else if (t.node.first == "factor") {
    if (t.node.second == "ID") {
      if (!(symtab.count(funcname))) throw string("ERROR");
      if (!(symtab.at(funcname).count(t.children.front().node.second))) throw string("ERROR");
      return symtab.at(funcname).at(t.children.front().node.second).first;
    } else if (t.node.second == "NUM") {
      return "int";
    } else if (t.node.second == "NULL") {
      return "int*";
    } else if (t.node.second == "LPAREN expr RPAREN") {
      return findtype(childrenAt(t,1));
    } else if (t.node.second == "AMP lvalue") {
      if(findtype(childrenAt(t,1)) == "int") {
        return "int*";
      } else throw string("ERROR");;
    } else if (t.node.second == "STAR factor") {
      if(findtype(childrenAt(t,1)) == "int*") {
        return "int";
      } else throw string("ERROR");
    } else if (t.node.second == "NEW INT LBRACK expr RBRACK") {
      if (findtype(childrenAt(t,3)) == "int") {
        return "int*";
      } else throw string("ERROR");
    } else if (t.node.second == "ID LPAREN RPAREN") {
      string procname = t.children.front().node.second;
      if ((!signatures.count(procname)) || (signatures.at(procname) != 0)) {
        throw string("ERROR");
      }
      return "int";
    } else if (t.node.second == "ID LPAREN arglist RPAREN") {
      string procname = (childrenAt(t,0).node).second;
      if (!signatures.count(procname)) {
        throw string("ERROR");
      }
      if (!goodtype(t)) throw string("ERROR");
      return "int";
    }
  } else throw string("ERROR");
}

//a recursion to build the tree
void insert(Tree& t) {
  if (isterm(t.node.first)) {
    return;
  }
  stringstream ss{t.node.second};
  string sym,line;
  while (ss >> sym) {
    if (!getline(cin,line)) throw string("ERROR");
    stringstream fromss{line};
    string from;
    if ((fromss >> from) && (from == sym)) {
      if (line.length() <= from.length()) {
        line = "";
      } else {
        line = line.substr(from.length()+1,(line.length()-from.length())-1);
      }
      pair<string,string> newnode (from,line);
      Tree newt(newnode);
      if ((t.node.first == "main") && (t.children.size() == 0)) {
        offset = 0;
        funcname = "wain";
        if (!symtab.count(funcname)) {
          symtab[funcname];
          pair<string,list<string>> newfunc;
          newfunc.first = funcname;
          symtabOrder.emplace_back(newfunc);
        } else throw string("ERROR");
      } else if ((t.node.first == "procedure") && (t.children.size() == 2)) {
        offset = 0;
        funcname = t.children.back().node.second;
        if (!symtab.count(funcname)) {
          symtab[funcname];
          pair<string,list<string>> newfunc;
          newfunc.first = funcname;
          symtabOrder.emplace_back(newfunc);
        } else throw string("ERROR");
      }
      insert(newt);
      t.children.emplace_back(newt);
      if ((t.node.second == "type ID") && (t.children.size() == 2)) {
        if ((funcname == "") || (!(symtab.count(funcname)))) throw string("ERROR");
        string typeterm = t.children.front().node.second;
        if (typeterm == "INT") {
          type = "int";
        } else if (typeterm == "INT STAR") {
          type = "int*";
        }
        varname = t.children.back().node.second;
        if (symtab.at(funcname).count(varname)) throw string("ERROR");
        pair<string,int> dcl (type,offset);
        offset -= 4;
        (symtab.at(funcname))[varname] = dcl;
        symtabOrder.back().second.emplace_back(varname);
      } else if ((t.node.first == "dcls") && (t.node.second != "") && (t.children.size() == 4)) {
        if ((funcname == "") || (!(symtab.count(funcname)))) throw string("ERROR");
        if ((varname == "") || (!(symtab.at(funcname).count(varname)))) throw string("ERROR");
      } else if ((((t.node.first == "lvalue") && (t.node.second == "ID")) ||
                  ((t.node.first == "factor") && (t.node.second == "ID"))) &&
                 (t.children.size() == 1)) {
        string id = t.children.front().node.second;
        if ((funcname == "") || (!(symtab.count(funcname)))) throw string("ERROR");
        if (!(symtab.at(funcname).count(id))) throw string("ERROR");
      } else if ((t.node.first == "main") && (t.children.size() == 6)) {
        if ((funcname == "") || (!(symtab.count(funcname)))) throw string("ERROR");
        if (signatures.count(funcname)) throw string("ERROR");
        signatures[funcname] = 2;
      } else if ((t.node.first == "procedure") && (t.children.size() == 4)) {
        if ((funcname == "") || (!(symtab.count(funcname)))) throw string("ERROR");
        int numSign = symtab.at(funcname).size();
        if (signatures.count(funcname)) throw string("ERROR");
        signatures[funcname] = numSign;
      } else if (((t.node.second == "ID LPAREN RPAREN") ||
                  (t.node.second == "ID LPAREN arglist RPAREN")) &&
                 (t.children.size() == 1)) {
        string procname = t.children.front().node.second;
        if (!(symtab.count(procname))) throw string("ERROR");
        if ((funcname == "") || (!(symtab.count(funcname)))) throw string("ERROR");
        if (symtab.at(funcname).count(procname)) throw string("ERROR");
      }
    } else throw string("ERROR");
  }
}

void push(int reg) {
  cout << "sw $" << reg << ",-4($30)" << endl;
  cout << "sub $30,$30,$4" << endl;
}

void pop(int reg) {
  cout << "add $30,$30,$4" << endl;
  cout << "lw $" << reg << ",-4($30)" << endl;
}

void proceduresCode(Tree& t) {
  if (t.node.second == "procedure procedures") {
    string function = funcname;
    funcname = childrenAt(childrenAt(t,0),1).node.second;
    procCalls.push(funcname);
    procedureCode(childrenAt(t,0));
    procCalls.pop();
    funcname = function;
    proceduresCode(childrenAt(t,1));
  } else if (t.node.second == "main") {
    string function = funcname;
    funcname = "wain";
    procCalls.push("wain");
    mainCode(childrenAt(t,0));
    procCalls.pop();
    funcname = function;
  } else throw string("ERROR");
}

void procedureCode(Tree& t) {
  if (t.node.first == "procedure") {
    string functionName = childrenAt(t,1).node.second;
    cout << "F" << functionName << ": ";
    dclsCode(childrenAt(t,6));
    stmtsCode(childrenAt(t,7));
    exprCode(childrenAt(t,9));
    cout << "jr $31" << endl;
  } else throw string("ERROR");
}

void mainCode(Tree& t) {
  if (t.node.first == "main") {
    cout << "Fwain: ";
    push(29);
    cout << "sub $29,$30,$4" << endl;
    push(1);
    push(2);
    if (childrenAt(childrenAt(t,3),0).node.second == "INT") {
      cout << "add $2,$0,$0" << endl;
    }
    push(31);
    cout << "lis $10" << endl;
    cout << ".word init" << endl;
    cout << "jalr $10" << endl;
    pop(31);
    dclsCode(childrenAt(t,8));
    stmtsCode(childrenAt(t,9));
    exprCode(childrenAt(t,11));
    cout << "add $30,$29,$4" << endl;
    pop(29);
    cout << "add $5,$0,$0" << endl;
    cout << "add $8,$0,$0" << endl;
    cout << "add $10,$0,$0" << endl;
  } else throw string("ERROR");
}

void dclsCode(Tree& t) {
  if (t.node.second == "") {
    return;
  } else if (t.node.second == "dcls dcl BECOMES NUM SEMI") {
    dclsCode(childrenAt(t,0));
    cout << "lis $3" << endl;
    cout << ".word " << childrenAt(t,3).node.second << endl;
    push(3);
  } else if (t.node.second == "dcls dcl BECOMES NULL SEMI") {
    dclsCode(childrenAt(t,0));
    push(11);
  } else throw string("ERROR");
}

void stmtsCode(Tree& t) {
  if (t.node.second == "") {
    return;
  } else if (t.node.second == "statements statement") {
    stmtsCode(childrenAt(t,0));
    stmtCode(childrenAt(t,1));
  } else throw string("ERROR");
}

void stmtCode(Tree& t) {
  if (t.node.second == "lvalue BECOMES expr SEMI") {
    lvalCode(childrenAt(t,0));
    push(3);
    exprCode(childrenAt(t,2));
    pop(5);
    cout << "sw $3,0($5)" << endl;
  } else if (t.node.second == "IF LPAREN test RPAREN LBRACE statements RBRACE ELSE LBRACE statements RBRACE") {
    int outerifcount = ifcount;
    ifcount++;
    testCode(childrenAt(t,2));
    cout << "beq $3,$0,else" << outerifcount << endl;
    stmtsCode(childrenAt(t,5));
    cout << "beq $0,$0,endif" << outerifcount << endl;
    cout << "else" << outerifcount << ":" << endl;
    stmtsCode(childrenAt(t,9));
    cout << "endif" << outerifcount << ":" << endl;
  } else if (t.node.second == "WHILE LPAREN test RPAREN LBRACE statements RBRACE") {
    int outerloopcount = loopcount;
    loopcount++;
    cout << "loop" << outerloopcount << ": ";
    testCode(childrenAt(t,2));
    cout << "beq $3,$0,endloop" << outerloopcount << endl;
    stmtsCode(childrenAt(t,5));
    cout << "beq $0,$0,loop" << outerloopcount << endl;
    cout << "endloop" << outerloopcount << ":" << endl;
  } else if (t.node.second == "PRINTLN LPAREN expr RPAREN SEMI") {
    exprCode(childrenAt(t,2));
    cout << "add $1,$3,$0" << endl;
    push(31);
    cout << "lis $10" << endl;
    cout << ".word print" << endl;
    cout << "jalr $10" << endl;
    pop(31);
  } else if (t.node.second == "DELETE LBRACK RBRACK expr SEMI") {
    exprCode(childrenAt(t,3));
    int delc = delcount;
    delcount++;
    cout << "beq $3,$11,endDel" << delc << endl;
    cout << "add $1,$3,$0" << endl;
    push(31);
    cout << "lis $10" << endl;
    cout << ".word delete" << endl;
    cout << "jalr $10" << endl;
    pop(31);
    cout << "endDel" << delc << ":" << endl;
  } else throw string("ERROR");
}

void lvalCode(Tree& t) {
  if (t.node.second == "ID") {
    string id = childrenAt(t,0).node.second;
    string function = procCalls.top();
    int lvaloffset = symtab.at(function).at(id).second;
    cout << "lis $3" << endl;
    cout << ".word " << lvaloffset << endl;
    cout << "add $3,$29,$3" << endl;
  } else if (t.node.second == "STAR factor") {
    factCode(childrenAt(t,1));
  } else if (t.node.second == "LPAREN lvalue RPAREN") {
    lvalCode(childrenAt(t,1));
  } else throw string("ERROR");
}

void factCode(Tree& t) {
  if (t.node.second == "ID") {
    string id = childrenAt(t,0).node.second;
    string function = procCalls.top();
    int lvaloffset = symtab.at(function).at(id).second;
    cout << "lw $3," << lvaloffset << "($29)" << endl;
  } else if (t.node.second == "NUM") {
    cout << "lis $3" << endl;
    cout << ".word " << childrenAt(t,0).node.second << endl;
  } else if (t.node.second == "NULL") {
    cout << "add $3,$11,$0" << endl;
  } else if (t.node.second == "LPAREN expr RPAREN") {
    exprCode(childrenAt(t,1));
  } else if (t.node.second == "AMP lvalue") {
    lvalCode(childrenAt(t,1));
  } else if (t.node.second == "STAR factor") {
    factCode(childrenAt(t,1));
    cout << "lw $3,0($3)" << endl;
  } else if (t.node.second == "NEW INT LBRACK expr RBRACK") {
    exprCode(childrenAt(t,3));
    cout << "add $1,$3,$0" << endl;
    push(31);
    cout << "lis $10" << endl;
    cout << ".word new" << endl;
    cout << "jalr $10" << endl;
    cout << "bne $3,$0,endif" << ifcount << endl;
    cout << "add $3,$11,$0" << endl;
    cout << "endif" << ifcount << ":" << endl;
    ifcount++;
    pop(31);
  } else if (t.node.second == "ID LPAREN RPAREN") {
    string function = childrenAt(t,0).node.second;
    procCalls.push(function);
    push(31);
    cout << "lis $10" << endl;
    cout << ".word F" << function << endl;
    push(29);
    cout << "sub $29,$30,$4" << endl;
    cout << "jalr $10"  << endl;
    cout << "add $30,$29,$4" << endl;
    pop(29);
    procCalls.pop();
    pop(31);
  } else if (t.node.second == "ID LPAREN arglist RPAREN") {
    string function = childrenAt(t,0).node.second;
    push(31);
    push(29);
    cout << "sub $8,$30,$4" << endl;
    argspushCode(childrenAt(t,2));
    procCalls.push(function);
    cout << "add $29,$8,$0" << endl;
    cout << "lis $10" << endl;
    cout << ".word F" << function << endl;
    cout << "jalr $10"  << endl;
    cout << "add $30,$29,$4" << endl;
    pop(29);
    procCalls.pop();
    pop(31);
  } else throw string("ERROR");
}

void argspushCode(Tree& t) {
  exprCode(childrenAt(t,0));
  push(3);
  if (t.node.second == "expr COMMA arglist") {
    argspushCode(childrenAt(t,2));
  }
}

void testCode(Tree& t) {
  exprCode(childrenAt(t,0));
  push(3);
  exprCode(childrenAt(t,2));
  pop(5);
  if (t.node.second == "expr EQ expr") {
    cout << "add $6,$0,$0" << endl;
    cout << "add $7,$0,$0" << endl;
    if (findtype(childrenAt(t,0)) == "int") {
      cout << "slt $6,$3,$5" << endl;
      cout << "slt $7,$5,$3" << endl;
    } else if (findtype(childrenAt(t,0)) == "int*") {
      cout << "sltu $6,$3,$5" << endl;
      cout << "sltu $7,$5,$3" << endl;
    } else throw string("ERROR");
    cout << "add $5,$6,$7" << endl;
    cout << "add $3,$0,$0" << endl;
    cout << "slt $3,$5,$11" << endl;
  } else if (t.node.second == "expr NE expr") {
    cout << "add $6,$0,$0" << endl;
    cout << "add $7,$0,$0" << endl;
    if (findtype(childrenAt(t,0)) == "int") {
      cout << "slt $6,$3,$5" << endl;
      cout << "slt $7,$5,$3" << endl;
    } else if (findtype(childrenAt(t,0)) == "int*") {
      cout << "sltu $6,$3,$5" << endl;
      cout << "sltu $7,$5,$3" << endl;
    } else throw string("ERROR");
    cout << "add $3,$6,$7" << endl;
  } else if (t.node.second == "expr LT expr") {
    cout << "add $6,$0,$0" << endl;
    if (findtype(childrenAt(t,0)) == "int") {
      cout << "slt $6,$5,$3" << endl;
    } else if (findtype(childrenAt(t,0)) == "int*") {
      cout << "sltu $6,$5,$3" << endl;
    } else throw string("ERROR");
    cout << "add $3,$6,$0" << endl;
  } else if (t.node.second == "expr LE expr") {
    cout << "add $6,$0,$0" << endl;
    if (findtype(childrenAt(t,0)) == "int") {
      cout << "slt $6,$3,$5" << endl;
    } else if (findtype(childrenAt(t,0)) == "int*") {
      cout << "sltu $6,$3,$5" << endl;
    } else throw string("ERROR");
    cout << "add $7,$0,$0" << endl;
    cout << "slt $7,$6,$11" << endl;
    cout << "add $3,$7,$0" << endl;
  } else if (t.node.second == "expr GT expr") {
    cout << "add $6,$0,$0" << endl;
    if (findtype(childrenAt(t,0)) == "int") {
      cout << "slt $6,$3,$5" << endl;
    } else if (findtype(childrenAt(t,0)) == "int*") {
      cout << "sltu $6,$3,$5" << endl;
    } else throw string("ERROR");
    cout << "add $3,$6,$0" << endl;
  } else if (t.node.second == "expr GE expr") {
    cout << "add $6,$0,$0" << endl;
    if (findtype(childrenAt(t,0)) == "int") {
      cout << "slt $6,$5,$3" << endl;
    } else if (findtype(childrenAt(t,0)) == "int*") {
      cout << "sltu $6,$5,$3" << endl;
    } else throw string("ERROR");
    cout << "add $3,$0,$0" << endl;
    cout << "slt $3,$6,$11" << endl;
  } else throw string("ERROR");
}

void exprCode(Tree& t) {
  if (t.node.second == "term") {
    termCode(childrenAt(t,0));
  } else if (t.node.second == "expr PLUS term") {
    exprCode(childrenAt(t,0));
    if (findtype(childrenAt(t,2)) == "int*") {
      cout << "mult $3,$4" << endl;
      cout << "mflo $3" << endl;
    }
    push(3);
    termCode(childrenAt(t,2));
    pop(5);
    if (findtype(childrenAt(t,0)) == "int*") {
      cout << "mult $3,$4" << endl;
      cout << "mflo $3" << endl;
    }
    cout << "add $3,$5,$3" << endl;
  } else if (t.node.second == "expr MINUS term") {
    exprCode(childrenAt(t,0));
    push(3);
    termCode(childrenAt(t,2));
    pop(5);
    if ((findtype(childrenAt(t,0)) == "int*") && (findtype(childrenAt(t,2)) == "int")) {
      cout << "mult $3,$4" << endl;
      cout << "mflo $3" << endl;
    }
    cout << "sub $3,$5,$3" << endl;
    if ((findtype(childrenAt(t,0)) == "int*") && (findtype(childrenAt(t,2)) == "int*")) {
      cout << "div $3,$4" << endl;
      cout << "mflo $3" << endl;
    }
  } else throw string("ERROR");
}

void termCode(Tree& t) {
  if (t.node.second == "factor") {
    factCode(childrenAt(t,0));
  } else if (t.node.second == "term STAR factor") {
    termCode(childrenAt(t,0));
    push(3);
    factCode(childrenAt(t,2));
    pop(5);
    cout << "mult $5,$3" << endl;
    cout << "mflo $3" << endl;
  } else if (t.node.second == "term SLASH factor") {
    termCode(childrenAt(t,0));
    push(3);
    factCode(childrenAt(t,2));
    pop(5);
    cout << "div $5,$3" << endl;
    cout << "mflo $3" << endl;
  } else if (t.node.second == "term PCT factor") {
    termCode(childrenAt(t,0));
    push(3);
    factCode(childrenAt(t,2));
    pop(5);
    cout << "div $5,$3" << endl;
    cout << "mfhi $3" << endl;
  } else throw string("ERROR");
}

int main() {
  try {
    string line;
    if(!getline(cin,line)) {
      return 1;
    }
    if (line != "start BOF procedures EOF") throw string("ERROR");
    string fromstart;
    stringstream ruless{line};
    ruless >> fromstart;
    if (line.length() <= fromstart.length()) {
      line = "";
    } else {
      line = line.substr(fromstart.length()+1,(line.length()-fromstart.length())-1);
    }
    pair<string,string> start (fromstart,line);
    parse.node = start;
    insert(parse);
    if (!goodtype(parse)) throw string("ERROR");
    cout << ".import print" << endl;
    cout << ".import init" << endl;
    cout << ".import new" << endl;
    cout << ".import delete" << endl;
    cout << "lis $4" << endl;
    cout << ".word 4" << endl;
    cout << "lis $11" << endl;
    cout << ".word 1" << endl;
    push(31);
    cout << "beq $0,$0,Fwain" << endl;
    proceduresCode(childrenAt(parse,1));
    pop(31);
    cout << "add $4,$0,$0" << endl;
    cout << "add $11,$0,$0" << endl;
    cout << "jr $31" << endl;
  } catch (string &msg) {
    cerr << msg << endl;
  }
}