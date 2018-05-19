#include <iostream>
#include <map>
#include <sstream>
#include <string>
#include <utility>
#include <list>
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

string funcname = "";
string varname = "";
string type = "";
string callproc = "";
int offset = 0;
list<pair<string,list<string>>>::iterator argprocit;
list<string>::iterator argit;

bool isterm(string& s);
Tree& childrenAt(Tree& t,int n);
bool goodtype(Tree& t);
string findtype(Tree& t);
void insert(Tree& t);
//void asm(Tree& t);

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
    good = (findtype(childrenAt(t,0)) == *argit);
    if (t.node.second == "expr") {
      ++argit;
      good = (good && (argit == (argprocit->second).end()));
    } else if (t.node.first == "expr COMMA arglist") {
      ++argit;
      good = (good && goodtype(childrenAt(t,2)) && (argit == (argprocit->second).end()));
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
        pair<string,int> dcl;
        dcl.first = type;
        (symtab.at(funcname))[varname] = dcl;
        symtabOrder.back().second.emplace_back(varname);
      } else if ((t.node.first == "dcls") && (t.node.second != "") && (t.children.size() == 4)) {
        if ((funcname == "") || (!(symtab.count(funcname)))) throw string("ERROR");
        if ((varname == "") || (!(symtab.at(funcname).count(varname)))) throw string("ERROR");
        string value = t.children.back().node.first;
        symtab.at(funcname).at(varname).second = offset;
        offset += 4;
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

/*void asm(Tree& t) {
  if (t.node.second == "procedure procedures") {
    asm(childrenAt(t,1));
  } else if (t.node.second == "main") {
    asm(childrenAt(t,0));
  } else if (t.node.first == "main") {
    ;
  } else if ((t.node.first == "type") && (t.node.second == "INT")) {
    ;
  } else if ((t.node.first == "dcls") && (t.node.second == "")) {
    ;
  } else if ((t.node.first == "dcl") && (t.node.second == "type ID")) {
    ;
  } else if ((t.node.first == "statements") && (t.node.second == "")) {
    ;
  } else if ((t.node.first == "expr") && (t.node.second == "term")) {
    ;
  } else if ((t.node.first == "term") && (t.node.second == "factor")) {
    ;
  } else if ((t.node.first == "factor") && (t.node.second == "ID")) {
    ;
  }
}

"add $3, ??, $0"
main INT WAIN LPAREN dcl COMMA dcl RPAREN LBRACE dcls statements RETURN expr SEMI RBRACE
type INT
dcls 
dcl type ID
statements 
expr term
term factor
factor ID
*/
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

//    asm(childrenAt(parse,1));

  } catch (string &msg) {
    cerr << msg << endl;
  }
}