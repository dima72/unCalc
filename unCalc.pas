unit unCalc;
{
  MIT License

  Author: Dmitry Konnov RU
  Copyright (c) 2022 Dmitry Konnov RU

  Permission is hereby granted, free of charge, to any person obtaining a copy
  of this software and associated documentation files (the "Software"), to deal
  in the Software without restriction, including without limitation the rights
  to use, copy, modify, merge, publish, distribute, sublicense, and/or sell
  copies of the Software, and to permit persons to whom the Software is
  furnished to do so, subject to the following conditions:

  The above copyright notice and this permission notice shall be included in all
  copies or substantial portions of the Software.

  THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
  IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,
  FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE
  AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER
  LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM,
  OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE
  SOFTWARE.
}

{$ObjExportAll On}
{$ZEROBASEDSTRINGS ON}

interface

uses
  SysUtils, Classes, Generics.Collections, unCalcUtil;

type
  PDoubleArray = ^TDoubleArray;
  TDoubleArray = array[0..MaxListSize-1] of extended;
  TOnVariableFoundEvent = procedure(Sender: TObject; const varName: string; var RetVal: extended) of Object;
  TNParFunc = function(const x: array of extended): extended;

  TNode = class(TObject)
    public
    function GetValue: extended; virtual; abstract;
    function IsUsed(Addr: Pointer): Boolean; virtual; abstract;
    procedure Optimize; virtual; abstract;
  end;

  type //A record that associates a function's memory address with the number of parameters it accepts.
    TNParFuncRecord = record
      Func   : TNParFunc;
      nParam : Integer;
    end;
    PNParamFuncRecord = ^TNParFuncRecord;

  type
    TunCalc = class(TComponent)
    private
      FOptimizationOn: Boolean;
      FNode: TNode;
      FDirty: Boolean;
      FNParFuncs: TDictionary<string, PNParamFuncRecord>;
      FVariables: TDictionary<string, PEXTENDED>;
      FOnVariableFound: TOnVariableFoundEvent;
    protected
      FExpression: string;
      function CreateParseTree(const AFormulaText: string; var ANode: TNode): Boolean;
      function IsTwoParamFunc(const AFormula: string;
        var AParamLeft, AParamRight: string;  var AFuncAddr: TNParFunc;
        ACurrChar: Integer ): Boolean;
      function IsOneParamFunc(const AFormula: string;
        var AParam: string;  var AFuncAddr: TNParFunc; ACurrChar: Integer ): Boolean;
      function IsNParamFunc(const AFormula: string; var AParams: TStringList;
         var AFuncAddr: TNParFunc): Boolean;
      function FindLastOper(const AFormula: string): Integer;
      procedure Optimize;
      function GetExpression: string;
      procedure SetExpression(const AStr: string); virtual;
      function GetX: extended;
      procedure SetX(const x: extended);
      function GetY: extended;
      procedure SetY(const y: extended);
    public
      constructor Create(AOwner: TComponent); override;
      destructor Destroy; override;
      procedure CreateVar(const AName: string; const AValue: extended); virtual;
      function Evaluate: extended; virtual;
      procedure Parse; virtual;
      procedure CreateDefaultVars; virtual;
      procedure CreateNParamFunc(const AName: string; AProcAddr: TNParFunc; ANparam: Integer); virtual;
      procedure CreateDefaultFuncs; virtual;
      procedure AssignVar(const AName: string; AVal: extended); virtual;
      function GetVar(const AName: string): extended; virtual;
      procedure DeleteVar(const AName: string); virtual;
      procedure DeleteAllVars; virtual;
      procedure DeleteFunc(const AName: string); virtual; //one param or two param, does not matter.
      procedure DeleteAllFuncs; virtual;
      function GetFunctions: TStringList; virtual;
      function GetVariables: TStringList; virtual;
      function GetVariablesUsed: TStringList; virtual;
      procedure Randomize; virtual;
      procedure FreeParseTree; virtual;
      property Value: extended read Evaluate;
      property Variable[const AName: string]: extended read GetVar write AssignVar;
      function IsVariableUsed(const AVarName: string): Boolean; virtual;
      function IsFunctionUsed(const AFuncName: string): Boolean; virtual;
      function IsVariable(const AVarName: string): Boolean;
      function IsNParamFunction(const AFuncName: string): Boolean;
      function IsFunction(const AFuncName: string): Boolean;
    published
      property Expression: string read GetExpression write SetExpression;
      property OptimizationOn: Boolean read FOptimizationOn write FOptimizationOn default True;
      property X: extended read GetX write SetX;
      property Y: extended read GetY write SetY;
      property OnVariableFound: TOnVariableFoundEvent read FOnVariableFound write FOnVariableFound;
    end;

  type
    TBasicNode = class(TNode)
    private
      Value: extended;
    public
      function GetValue: extended; override;
      function IsUsed(Addr: Pointer): Boolean; override;
      procedure Optimize; override; //Optimize performs compile-time evaluation of constant values.
      constructor Create(AVal: extended);
      destructor Destroy; override;
    end;

  type
    TParamNode = class(TNode)
    private
      Children: TList<TNode>;
      Func: TNParFunc;
    public
      function GetValue: extended; override;
      function IsUsed(Addr: Pointer): Boolean; override;
      procedure Optimize; override; //Optimize performs compile-time evaluation of constant values.
      constructor Create(var ANodes: TList<TNode>; AFuncAddr: TNParFunc);
      destructor Destroy; override;
    end;

  type //a variable node
    TVarNode = class(TNode)
    private
      pVar   : PEXTENDED;   //The variable's memory address within the variable list.
    public
      function GetValue: extended; override;
      function IsUsed(Addr: Pointer): Boolean; override;
      procedure Optimize; override; //Optimize performs compile-time evaluation of constant values.
      constructor Create(variable: PEXTENDED);
      destructor Destroy; override;
    end;

  type //a variable node
    TUnknownVarNode = class(TNode)
    private
      VarName   : string;
      MathParser: TunCalc; // current parser.
    public
      function GetValue: extended; override;
      function IsUsed(AAddr: Pointer): Boolean; override;
      procedure Optimize; override; //Optimize performs compile-time evaluation of constant values.
      constructor Create(AParser: TunCalc; AVariableName: string);
      destructor Destroy; override;
    end;

implementation

threadvar
  VariableToSearchFor: string; //to implement TUnknownVarNode.IsUsed. hack

procedure DisposeList(var AList: TList<TNode>);
  var i: Integer;
begin
  for i := AList.Count-1 downto 0 do
  begin
   TObject(AList[i]).Free;
   AList.Delete(i);
  end;
  AList.Free;
  AList := nil;
end;

procedure OptimizeNode(var ANode: TNode);//a global function that optimizes any given tree branch
var
  NewNode: TBasicNode;
  NparamNode: TParamNode;
  i: Integer;
begin
  ANode.Optimize; //will call Optimize for all nodes in the tree.
  if (ANode is TParamNode) then
  begin
    NparamNode := ANode as TParamNode;
    for i := NparamNode.Children.Count-1 downto 0 do
    begin
      if not (TNode(NparamNode.Children.Items[i]) is TBasicNode) then
        exit; //this is not a basic node, exit.
    end;
    //if we arrive here, means all children are basic nodes:
    NewNode := TBasicNode.Create(NparamNode.GetValue);
    ANode.Free;
    ANode := NewNode;
  end;
end;

procedure FindVariablesUsed(var ANode: TNode; var AVarList: TStringList);
var
  ChildNode: TNode;
  NparamNode: TParamNode;
  UnknownVarNode: TUnknownVarNode;
  i: Integer;
begin
  if (ANode is TUnknownVarNode) then
  begin
    UnknownVarNode := ANode as TUnknownVarNode;
    AVarList.Add(UnknownVarNode.VarName);
  end
  else if (ANode is TParamNode) then
  begin
    NparamNode := ANode as TParamNode;
    for i := NparamNode.Children.Count-1 downto 0 do
    begin
      ChildNode := TNode(NparamNode.Children.Items[i]);
      FindVariablesUsed(ChildNode, AVarList);
    end;
  end;
end;

constructor TBasicNode.Create(AVal: extended);
begin
  inherited Create;
  Value := AVal;
end;

destructor TBasicNode.Destroy;
begin
  inherited Destroy;
end;

function TBasicNode.GetValue;
begin
  Result := Value;
end;

function TBasicNode.IsUsed(Addr: Pointer): Boolean;
begin
  Result := False; //a basic node does not store any variable or function info
end;

procedure TBasicNode.Optimize;
begin
  //do nothing.
end;

constructor TParamNode.Create(var ANodes: TList<TNode>; AFuncAddr: TNParFunc);
begin
  inherited Create;
  Children := ANodes;
  Func  := AFuncAddr;
end;

destructor TParamNode.Destroy;
var
  i: Integer;
begin
  for i := Children.Count - 1 downto 0 do
  begin
    Children[i].Free;
  end;
  Children.Free;
  inherited Destroy;
end;

function TParamNode.GetValue;
var
  ArrayValues: array of extended;
  i: Integer;
  fVal: extended;
begin
  SetLength(ArrayValues, Children.Count);
  for i := 0 to Children.Count - 1 do
  begin
    fVal := Children[i].GetValue;
    ArrayValues[i] := fVal;
  end;
  Result := Func(ArrayValues);
end;

function TParamNode.IsUsed(Addr: Pointer): Boolean;
var
  i: Integer;
begin
  Result := (Addr = @Func);
  for i := 0 to Children.Count-1 do
  begin
    if (TNode(Children.Items[i])).IsUsed(Addr) then
    begin
      Result := True;
      exit;
    end;
  end;
end;

procedure TParamNode.Optimize; //Evaluates constant values at compile time.
var
  i: Integer;
  Node: TNode;
begin
  for i := 0 to Children.Count - 1 do
  begin
    Node := TNode(Children.Items[i]);
    OptimizeNode(Node);
    Children.Items[i] := Node;
  end;
end;

constructor TVarNode.Create(variable: PEXTENDED);
begin
  inherited Create;
  pVar := variable;
end;

destructor TVarNode.Destroy;
begin
  inherited Destroy;
end;

function TVarNode.GetValue;
begin
  Result := pVar^;
end;

function TVarNode.IsUsed(Addr: Pointer): Boolean;
begin
  Result := (Addr = pVar);
end;

procedure TVarNode.Optimize;
begin
  //do nothing
end;

constructor TUnknownVarNode.Create(AParser: TunCalc; AVariableName: string);
begin
  inherited Create;
  MathParser := AParser;
  VarName := AVariableName;
end;

destructor TUnknownVarNode.Destroy;
begin
  inherited Destroy;
end;

function TUnknownVarNode.GetValue;
begin
  Result := 0.0;
  MathParser.OnVariableFound(MathParser, VarName, Result);
end;

function TUnknownVarNode.IsUsed(AAddr: Pointer): Boolean;
begin
  if (AAddr = nil) and (VariableToSearchFor = VarName) then
    Result := True
  else
    Result := False; //this method is not supported for TUnknownVarNode type.
end;

procedure TUnknownVarNode.Optimize;
begin
  //do nothing
end;

constructor TunCalc.Create(AOwner: TComponent);
begin
  inherited Create(AOwner);
  FExpression := '';
  FNode := nil;
  FDirty := True; //Parser's status - not parsed yet.
  FOptimizationOn := True;
  FVariables := TDictionary<string, PEXTENDED>.Create;
  FNParFuncs := TDictionary<string, PNParamFuncRecord>.CReate;
  CreateDefaultFuncs;
  CreateDefaultVars;
end;

destructor TunCalc.Destroy;
begin
  FNode.Free;
  DeleteAllVars; //free all pointers that hold numbers.
  DeleteAllFuncs;
  FVariables.Free;
  FNParFuncs.Free;
  inherited Destroy;
end;

procedure TunCalc.Parse;
var
  TempStr: string;
  i, LastIndex, iBrackets: Integer;
begin
  if not (Length(FExpression) > 0) then
  begin
   FNode.Free; //free doesn't assign nil to the pointer...
   FNode := nil; //must assign NULL to avoid Exception if object doesn't exist.
   CheckError(False, 'Expression is empty.', '', '');
  end;
  //Check for uppercase version of function defs
  TempStr := UpperCase(FExpression); //FExpression is a member variable of the class
  //replace space chars with empty string
  TempStr := stringReplace(TempStr, ' ', '', [ rfReplaceAll ] ); //eat the spaces
  // This has issues with 0 based strings and immutable string that are coming.
  LastIndex := Length(TempStr) - 1;
  for i := 0 to LastIndex do
  begin
  if (TempStr[i] = '[') or (TempStr[i] = '{') then
    TempStr[i] := '('
  else if (TempStr[i] = ']') or (TempStr[i] = '}') then
    TempStr[i] := ')';
  end;
  FNode.Free; //free the previous parse tree
  FNode := nil; //must assign NULL to avoid Exception if object doesn't exist.
  iBrackets := CheckBrackets(TempStr);
  if (iBrackets > -1) and (iBrackets<LastIndex + 1) then
    raise EunCalcError.Create(Format('Bracket mismatch in expression %s at index %s.',
      [TempStr, IntToStr(iBrackets)]), TempStr.Substring(0, iBrackets), TempStr)
  else if(iBrackets = LastIndex) then
    raise EunCalcError.Create(Format('Missing bracket ")" in expression %s.', [TempStr]), TempStr, TempStr);
  //recursive CreateParseTree method generates the node structure tree
  if not CreateParseTree(TempStr, FNode) then
  begin
    FNode.Free;
    FNode := nil;
    CheckError(False, 'Syntax error in expression ' + FExpression, TempStr, TempStr);
  end;
  if FOptimizationOn then
    Optimize;
  FDirty := False; //Unless the expression is changed we do not need to reparse it.
end;

function TunCalc.Evaluate: extended;
begin
  if (FDirty) then //if the expression has been changed, we need to parse it again
    Parse;
  //this will start the chain reaction to get the value of all nodes
  Result := FNode.GetValue;
end;

function TunCalc.FindLastOper(const AFormula: string): Integer;
var
  i, j, BracketLevel, Precedence, LastWasOperator, PrevOperIndex, LastIndex: Integer;
  ch: Char;
begin
  Precedence := 13; //There are 12 operands and 13 is higher then all
  BracketLevel := 0; //shows the level of brackets we moved through
  Result := -1;
  LastWasOperator := 0;
  LastIndex := Length(AFormula) - 1;
  for i := 0 to LastIndex do //from left to right scan...
  begin
    if LastWasOperator > 2 then
    begin
      Result := -1;
      exit;
    end;
    case AFormula[i] of
      ')': begin
              dec(BracketLevel);//counting bracket levels
              LastWasOperator := 0;
           end;
      '(': begin
              inc(BracketLevel);
              LastWasOperator := 0;
           end;
      '|': begin
             if not ((BracketLevel > 0) or (LastWasOperator > 0)) then //a main operation has to be outside the brackets
                if Precedence >= 1 then //seeking for lowest precedence
                begin
                     Precedence := 1;
                     Result := i; //record the current index.
                end;
             inc(LastWasOperator);
           end;
      '&': begin
             if not ((BracketLevel > 0) or (LastWasOperator > 0)) then //a main operation has to be outside the brackets
                if Precedence >= 2 then //seeking for lowest precedence
                begin
                     Precedence := 2;
                     Result := i; //record the current index.
                end;
             inc(LastWasOperator);
           end;
      '!': begin
             if not ((BracketLevel > 0) or (LastWasOperator > 0)) then //a main operation has to be outside the brackets
                if Precedence >= 3 then //seeking for lowest precedence
                begin
                     Precedence := 3;
                     Result := i; //record the current index.
                end;
             inc(LastWasOperator);
           end;
      '=': begin
             if not ((BracketLevel > 0) or (LastWasOperator > 0)) then //a main operation has to be outside the brackets
                if Precedence >= 4 then //seeking for lowest precedence
                begin
                     Precedence := 4;
                     Result := i; //record the current index.
                end;
             if(LastWasOperator > 0 )then
             begin
              PrevOperIndex := i - LastWasOperator;
              if not ((AFormula[PrevOperIndex] = '<') or (AFormula[PrevOperIndex] = '>')) then
              begin
                inc(LastWasOperator);
              end;
             end else begin
              inc(LastWasOperator);
             end;
           end;
           //need to correct the precedence of these folks:
      '>': begin
             if not ((BracketLevel > 0) or (LastWasOperator > 0)) then //a main operation has to be outside the brackets
                if Precedence >= 5 then //seeking for lowest precedence
                begin
                  Precedence := 5;
                  Result := i; //record the current index.
                end;
             if(LastWasOperator > 0) then
             begin
              if not (AFormula[i-LastWasOperator] = '<') then
              begin
                inc(LastWasOperator);
              end;
             end else
             begin
               inc(LastWasOperator);
             end;
           end;
      '<': begin
             if not ((BracketLevel > 0) or (LastWasOperator > 0)) then //a main operation has to be outside the brackets
                if Precedence >= 5 then //seeking for lowest precedence
                begin
                  Precedence := 5;
                  Result := i; //record the current index.
                end;
             inc(LastWasOperator);
           end;
      '-': begin
             if not ((BracketLevel > 0) or (LastWasOperator > 0)) then //a main operation has to be outside the brackets
                if (Precedence >= 7) then //seeking for lowest precedence
                begin
                  Precedence := 7;
                  Result := i; //record the current index.
                end;
             inc(LastWasOperator);
           end;
      '+': begin
             if not ((BracketLevel > 0) or (LastWasOperator > 0)) then //a main operation has to be outside the brackets
                if Precedence >= 7 then
                begin
                  Precedence := 7;
                  Result := i;
                end;
             inc(LastWasOperator);
           end;
      '%': begin
             if not ((BracketLevel > 0) or (LastWasOperator > 0)) then //a main operation has to be outside the brackets
                if Precedence >= 9 then
                begin
                  Precedence := 9;
                  Result := i;
                end;
             inc(LastWasOperator);
           end;
      '/': begin
             if not ((BracketLevel > 0) or (LastWasOperator > 0)) then //a main operation has to be outside the brackets
                if Precedence >= 9 then
                begin
                  Precedence := 9;
                  Result := i;
                end;
             inc(LastWasOperator);
           end;
      '*': begin
             if not ((BracketLevel > 0) or (LastWasOperator > 0)) then //a main operation has to be outside the brackets
                if Precedence >= 9 then
                begin
                  Precedence := 9;
                  Result := i;
                end;
             inc(LastWasOperator);
           end;
      '^': begin
             if not ((BracketLevel > 0) or (LastWasOperator > 0)) then //a main operation has to be outside the brackets
                if Precedence >= 12 then
                begin
                  Precedence := 12;
                  Result := i;
                end;
             inc(LastWasOperator);
           end;
      'E':
        if i > 0 then
        begin
          ch := AFormula[i - 1];
          if ((ch >= '0') and (ch <= '9')) then
          begin//this E may be part of a number in scientific notation.
            j := i;
            while(j > 1) do
            begin //trace back.
              dec(j);
              ch := AFormula[j];
              if ((ch = '.') or ((ch >= '0') and (ch <= '9'))) then
              begin //if it is not a function or variable name.
                continue;
              end;
              if ((ch = '_') or ((ch >= 'A') and (ch <= 'Z'))) then
              begin//is it a func or var name?
                LastWasOperator := 0;
                break; //break the while loop.
              end;
              inc(LastWasOperator); //it must be an operator or a paranthesis.
              break; //break the while loop.
            end;
            if ((j = 0) and ((ch >= '0') and (ch <= '9'))) then
              inc(LastWasOperator);
          end
          else
            LastWasOperator := 0;
        end
        else
          LastWasOperator := 0;
      ' ':
       begin
         //break;
       end ;
    else//case else
      LastWasOperator := 0;
    end;
  end;
end;

function TunCalc.IsOneParamFunc(const AFormula: string;
  var AParam: string; var AFuncAddr: TNParFunc; ACurrChar: Integer): Boolean;
var
  i, ParamStart, Len, ValidCount, LastIndex: Integer;
  Temp: string;
  PFuncRecord: PNParamFuncRecord;
begin
  Len := Length(AFormula);
  Result := False;
  if Len = 0 then
     exit;
  if Pos(',', AFormula) <> 0 then
     exit;
  LastIndex := Len - 1;
  if ACurrChar = 0 then //if function in question is an unary operand
  begin
    Result := True;
    AParam := AFormula.Substring(0+1, Len-1);
    if not (Length(AParam)>0) then
    begin
        Result := False;
        exit;
    end;
    case AFormula[ACurrChar] of
      '+': AFuncAddr := @_unaryadd;
      '-': AFuncAddr := @_negate;
      '!': AFuncAddr := @_not;
      else Result := False; //only + and - can be unary operators
    end;
    exit; //all output is assigned, now we exit.
  end;
  //if we reach here, result is False
  //if main operation is not an operand but a function
  if (AFormula[LastIndex] = ')') then //last character must be brackets closing function param list
  begin
    i := 0;
    ValidCount := 0;
    while IsValidChar(i, AFormula[i]) do
    begin
      CheckError(i < MAX_NAME_LEN, 'Function name in ' + AFormula +
        ' is too long. Maximum possible name length is ' + IntToStr(MAX_NAME_LEN) +
        '.', AFormula.Substring(0, MAX_NAME_LEN), AFormula);
      Inc(i);
      Inc(ValidCount);
    end;
    while AFormula[i] = ' ' do
     Inc(i);
    if (AFormula[i] = '(') and (i < LastIndex-1) then
    begin
      Temp := AFormula.Substring(0, ValidCount);
      if FNParFuncs.TryGetValue(Temp, PFuncRecord) then
      begin
        ParamStart := Succ(i);
         AFuncAddr := PFuncRecord^.Func;
        AParam := AFormula.Substring(ParamStart, LastIndex-ParamStart); //check example: SIN(30)
        Result := True //we are sure that it is a two parameter function
      end;
    end;
  end;
end;

//returns the last operation index in the string
function TunCalc.IsTwoParamFunc(const AFormula: string; var AParamLeft,
  AParamRight: string; var AFuncAddr: TNParFunc; ACurrChar: Integer): Boolean;
var
  i, BracketLevel, paramStart, Len, ValidCount, LastIndex: Integer;
  c, nextCh: char;
  Temp: string;
  PFuncRecord: PNParamFuncRecord;
begin
  Len := Length(AFormula);
  Result := False;
  if Len=0 then
     exit;
  if ACurrChar = -1 then
     exit;
  //if Expression is not in paretheses then check number of arguments
  if (AFormula[0] <> '(') and (AFormula[Len-1] <> ')') then
  begin
    i := Pos(',', AFormula);
    if (i <> 0) and (i < ACurrChar) then
    begin
       if Pos(',', AFormula, i) <> 0 then
         exit;
    end;
  end;
  LastIndex := Len - 1;
  if ACurrChar > -1 then //if function in question is an operand
  begin
    if(ACurrChar > LastIndex-1) then
    begin
      Result := False;
      exit;
    end;
    c := AFormula[ACurrChar];
    //was it an operand also? we want to find <>, >=, <=
    if(c = '<') then
    begin
      nextCh := AFormula[ACurrChar+1]; //look ahead.
      if(nextCh = '>')then
      begin
        AFuncAddr  := @_notequals;
        AParamLeft := AFormula.Substring(0, ACurrChar);
        AParamRight := AFormula.Substring(ACurrChar+2, Len - ACurrChar);
      end else if (nextCh='=') then
      begin
        AFuncAddr  := @_ltequals;
        AParamLeft := AFormula.Substring(0, ACurrChar);
        AParamRight := AFormula.Substring(ACurrChar + 2, Len - ACurrChar);
      end else
      begin
        AFuncAddr  := @_less; //default case.
        AParamLeft := AFormula.Substring(0, ACurrChar);
        AParamRight := AFormula.Substring(ACurrChar+1, Len - ACurrChar);
      end;
      if (not (Length(AParamLeft)>0) ) then
      begin
        Result := False;
        exit;
      end;
      if (not (Length(AParamRight)>0) ) then
      begin
        Result := False;
        exit;
      end;
      Result := True; //all output is assigned, now we return True.
      exit;
    end
    else if (c = '>') then
    begin
      nextCh := AFormula[ACurrChar+1];
      if(nextCh = '=') then
      begin
        AFuncAddr  := @_gtequals;
        AParamLeft := AFormula.Substring(0, ACurrChar);
        AParamRight := AFormula.Substring(ACurrChar+2, LastIndex-ACurrChar-1);
      end
      else
      begin
        AFuncAddr  := @_greater; //default case.
        AParamLeft := AFormula.Substring(0, ACurrChar);
        AParamRight := AFormula.Substring(ACurrChar+1, LastIndex - ACurrChar);
      end;
      if (not (Length(AParamLeft)>0) ) then
      begin
        Result := False;
        exit;
      end;
      if (not (Length(AParamRight)>0) ) then
      begin
        Result := False;
        exit;
      end;
      Result := True; //all output is assigned, now we return True.
      exit;
    end
    else
    begin //default case:
      Result := True;
      AParamLeft := AFormula.Substring(0, ACurrChar);
      if not (Length(AParamLeft)>0) then
      begin
        Result := False;
        exit;
      end;
      AParamRight := AFormula.Substring(ACurrChar + 1, LastIndex - ACurrChar);
      if not (Length(AParamRight)>0) then
      begin
        Result := False;
        exit;
      end;
      case c of
        //analytic operators:
        '+': AFuncAddr := @_add;
        '-': AFuncAddr := @_subtract;
        '*': AFuncAddr := @_multiply;
        '/': AFuncAddr := @_divide;
        '^': AFuncAddr := @_power;
        '%': AFuncAddr := @_intdiv;
        //logical operators:
        //'>': funcAddr := @_greater;
        //'<': funcAddr := @_less;
        '=': AFuncAddr := @_equal;
        '&': AFuncAddr := @_and;
        '|': AFuncAddr := @_or;
      end;
      exit; //all output is assigned, now we exit.
    end;
  end;
  //if we reach here, result is False
  //if main operation is not an operand but a function
  if (AFormula[LastIndex] = ')') then //last character must be brackets closing function param list
  begin
    i := 0;
    ValidCount := 0;
    while IsValidChar(i, AFormula[i]) do
    begin
      CheckError(i < MAX_NAME_LEN, 'Function name in ' + AFormula +
        ' is too long. Maximum possible name length is ' +
        IntToStr(MAX_NAME_LEN) + '.',  AFormula.Substring(0, MAX_NAME_LEN), AFormula);
      Inc(i);
      Inc(ValidCount);
    end;
    while AFormula[i] = ' ' do
    begin
     Inc(i);
    end;
    if (AFormula[i] = '(') and (i < LastIndex) then
    begin
      Temp := AFormula.Substring(0, ValidCount);
      if FNParFuncs.TryGetValue(Temp, PFuncRecord) then //FTwoParFuncs AFuncAddr
      begin
        paramStart := Succ(i);
        AFuncAddr := PFuncRecord^.Func;
        //Nparams := PFuncRecord^.nParam;
        BracketLevel := 1;
        while not (i>LastIndex-1) do //last character is a ')', that's why we use i>Len-1
        begin
          Inc(i);
          case AFormula[i] of
            '(': inc(BracketLevel);
            ')': dec(BracketLevel);
            ',': begin
                   if (BracketLevel = 1) and (i < LastIndex - 1) then //last character is a ')', that's why we use i>Len-1
                   begin
                      AParamLeft := AFormula.Substring(paramStart, i - paramStart);
                      AParamRight := AFormula.Substring(i+1, LastIndex - 1 - i); //last character is a ')', that's why we use Len-1-i
                      Result := True; //we are sure that it is a two parameter function
                   end;
                end;
          end;
        end;
      end;
    end;
  end;
end;

function TunCalc.IsNParamFunc(const AFormula: string; var AParams: TStringList;
  var AFuncAddr: TNParFunc): Boolean;
var
  i, BracketLevel, ParamStart, Len, Pindex, Nparams, ValidCount, LastIndex: Integer;
  PFuncRecord: PNParamFuncRecord;
  Temp: string;
begin
  Len := Length(AFormula);
  Result := False;
  if Len = 0 then
     exit;
  LastIndex := Len - 1;
  if (AFormula[LastIndex] = ')') then //last character must be brackets closing function param list
  begin
     i := 0;
     ValidCount := 0;
     while IsValidChar(i, AFormula[i]) do
     begin
       CheckError(i < MAX_NAME_LEN, 'Function name in ' + AFormula +
         ' is too long. Maximum possible name length is ' +
         IntToStr(MAX_NAME_LEN) + '.', AFormula.Substring(0, MAX_NAME_LEN), AFormula);
       Inc(i);
       Inc(ValidCount);
     end;
     while AFormula[i] = ' ' do
     begin
       Inc(i);
     end;
     if (AFormula[i] = '(') and (i < LastIndex) then
     begin
        Temp := AFormula.Substring(0, ValidCount);
        if FNParFuncs.TryGetValue(Temp, PFuncRecord) then
        begin
           ParamStart := Succ(i);
           AFuncAddr := PFuncRecord^.Func;
           Nparams := PFuncRecord^.nParam;
           begin
             AParams := TStringList.Create; //must not forget to free outside this function.
             BracketLevel := 1;
             Pindex := 0; //parameter index.
             while not (i > LastIndex) do //last character is a ')', that's why we use i>Len-1
             begin
                Inc(i);
                case AFormula[i] of
                '(': inc(BracketLevel);
                ')': begin
                      dec(BracketLevel);
                      if ((Nparams = -1) or (Nparams = 1)) and (BracketLevel = 0) then
                      begin
                        if ParamStart < i then
                        begin
                          // If we have reached the end, add the last param:
                          AParams.Add(AFormula.Substring(ParamStart, i - ParamStart));
                          Result := True;
                          exit;
                        end
                        else
                        begin
                          // We got no parameter text, it cannot be valid.
                          Result := False;
                          exit;
                        end;
                      end;
                    end;
                ',': begin
                       if (BracketLevel = 1) and (i < LastIndex - 1) then //last character is a ')', that's why we use i>Len-1
                       begin
                          if (Nparams <> -1) and not (Pindex < Nparams) then
                            Result := False //wrong number of parameters.
                          else
                          begin
                            AParams.Add(AFormula.Substring(ParamStart, i - ParamStart));
                            inc(Pindex);
                            if Pindex = Nparams-1 then
                            begin
                              //assign the last one:
                              AParams.Add(AFormula.Substring(i+1, LastIndex - 1 - i));
                              Result := True;
                              exit;
                            end;
                            ParamStart := i+1;
                          end;
                       end;
                    end;
                end;
             end;
           end;
        end;
     end;
  end;
end;

function TunCalc.CreateParseTree(const AFormulaText: string; var ANode: TNode): Boolean;
var
  fNum: extended;
  iLastOper: Integer;
  sParamLeft, sParamRight, Formula: string;
  slParams: TStringList;
  lNodes : TList<TNode>;
  oLeftNode, oRightNode  : TNode;
  funcAddr: Pointer;
  i: Integer;
  bWasChanged: Boolean;
  PNum: PEXTENDED;
begin
  Result := False;
  Formula := Trim(AFormulaText);
  if Formula = '' then  exit;
  bWasChanged := RemoveOuterBrackets(Formula); //remove unnecessary brackets
  if bWasChanged then
  begin
    Formula := Trim(Formula);
    if not (Length(Formula) > 0) then
      exit;
  end;
  //we should first remove brackets, and then check the formula length that might be modified
  //while removing brackets.
  //if brackets does not match then return False.
  if (CheckBrackets(Formula) <> -1) then exit;
  if IsValidNumber(Formula, fNum) then
  begin //if it is a simple number create a number node and attach it
    ANode := TBasicNode.Create(fNum);
    Result := True;
  end
  else if FVariables.TryGetValue(Formula, PNum) then
  begin//if it is not a simple number recursion will end on these points when we get to the basics
    ANode := TVarNode.Create(PNum);
    Result := True;
  end
  else if Assigned(OnVariableFound) and IsValidName(Formula) then
  begin//recursion will end on these points when we get to the basics
    ANode := TUnknownVarNode.Create(self, Formula);
    Result := True;
  end
  else //if it is not a variable
  begin
    iLastOper := FindLastOper(Formula);
    if not (iLastOper > 0) then //if it is 1 then it is a unary operation which is a one param function
    begin
      if IsOneParamFunc(Formula, sParamLeft, TNParFunc(funcAddr), iLastOper) then
      begin
        if not CreateParseTree(sParamLeft, oLeftNode) then
        begin
          FreeParseTree;
          CheckError(False, Format('Sub expression <%s> in <%s> is not valid.', [sParamLeft, Formula]), sParamLeft, Formula);
        end;
        lNodes := TList<TNode>.Create();
        lNodes.Add(oLeftNode);
        ANode := TParamNode.Create(lNodes, funcAddr);
        Result := True;
        exit; //if it is a one param function then we exit, otherwise below code will execute
      end;
    end;
    if IsTwoParamFunc(Formula, sParamLeft, sParamRight, TNParFunc(funcAddr), iLastOper) then
    begin
      if (not CreateParseTree(sParamLeft, oLeftNode)) then
      begin
        FreeParseTree;
        CheckError(False, Format('Sub expression <%s> in <%s> is not valid.', [sParamLeft, Formula]), sParamLeft, Formula);
      end;
      if (not CreateParseTree(sParamRight, oRightNode)) then
      begin
        FreeParseTree;
        CheckError(False, Format('Sub expression <%s> in <%s> is not valid.', [sParamRight, Formula]), sParamRight, Formula);
      end;
      lNodes := TList<TNode>.Create();
      lNodes.Add(oLeftNode);
      lNodes.Add(oRightNode);
      ANode := TParamNode.Create(lNodes, funcAddr);
      Result := True;
      exit;
    end;
    if IsNParamFunc(Formula, slParams, TNParFunc(funcAddr)) then
    begin
      if (slParams <> nil) then
      begin
        lNodes := TList<TNode>.Create();
        for i :=0 to slParams.Count-1 do
        begin
          sParamLeft := slParams[i];
          if not CreateParseTree(sParamLeft, oLeftNode) then
          begin
            DisposeList(lNodes);
            FreeParseTree;
            CheckError(False, Format('Sub expression <%s> in <%s> is not valid.', [sParamLeft, Formula]), sParamLeft, Formula);
          end;
          lNodes.Add(oLeftNode);
        end;
        ANode := TParamNode.Create(lNodes, funcAddr);
        slParams.Free;
        Result := True;
        exit;
      end;
    end;
  end;
  //if code reaches here it means we did not exit as a result of False expression.
end;

procedure TunCalc.CreateVar(const AName: string; const AValue: extended);
var
  p: PEXTENDED;
  UpcName: string;
begin
  CheckError(Length(AName) > MAX_NAME_LEN, AName + ' is too long. Maximum variable or function name length is ' +
      IntToStr(MAX_NAME_LEN) + '.', AName.Substring(0, MAX_NAME_LEN), AName);
  UpcName := UpperCase(AName);
  CheckError(IsValidName(UpcName), AName + ' is not a valid variable name.', AName, AName);
  if (FVariables.TryGetValue(UpcName, p)) then
    p^ := value
  else
  begin
    New(p);
    p^ := AValue;
    FVariables.Add(UpcName, p);
    FDirty := True; //previously bad expression may now be ok, we should reparse it
  end;
end;

procedure TunCalc.CreateNParamFunc(const AName: string; AProcAddr: TNParFunc; ANparam: Integer);
var
  PFuncRecord: PNParamFuncRecord;
  UpcName: string;
begin
  CheckError(Length(AName) > MAX_NAME_LEN, AName + ' is too long. Maximum variable or function name length is ' +
      IntToStr(MAX_NAME_LEN) + '.', AName.Substring(0, MAX_NAME_LEN), AName);
  UpcName := UpperCase(AName);
  CheckError(IsValidName(UpcName), AName + ' is not a valid function name.', AName, AName);
  New(PFuncRecord); //must deallocate using dispose()
  PFuncRecord^.Func := @AProcAddr;
  PFuncRecord^.nParam := ANparam;
  FNParFuncs.Add(UpcName, PFuncRecord); //add the variables and the object to hold the value with it.
  FDirty := True; //previously bad expression may now be ok, we should reparse it
end;

procedure TunCalc.AssignVar(const AName: string; AVal: extended);
var
  p: PEXTENDED;
begin
  if (FVariables.TryGetValue(UpperCase(AName), p)) then
    p^ := AVal
  else
    CreateVar(AName, AVal);//if not found, add the variable:
end;

function TunCalc.GetVar(const AName: string): extended;
var
  p: PEXTENDED;
begin
  CheckError(FVariables.TryGetValue(UpperCase(AName), p),
    Format('Variable %s is not found.', [AName]), AName, AName);
  Result := p^
end;

procedure TunCalc.DeleteVar(const AName: string);
var
  p: PEXTENDED;
  UpcName: string;
begin
  UpcName := UpperCase(AName);
  //this function deletes the variable only if it finds it.
  if (FVariables.TryGetValue(UpcName, p)) then
  begin
    Dispose(p);
    FVariables.Remove(UpcName);
    FDirty := True;
  end;
end;

procedure TunCalc.DeleteFunc(const AName: string);
var
  PFuncRecord: PNParamFuncRecord;
  UpcName: string;
begin
  UpcName := UpperCase(AName);
  FDirty := True;
  if (FNParFuncs.TryGetValue(UpcName, PFuncRecord)) then
  begin
   Dispose(PFuncRecord);
   FNParFuncs.Remove(UpcName);
  end
  else
   FDirty := False;//if nothing is deleted
end;

function TunCalc.GetExpression: string;
begin
  Result := FExpression;
end;

procedure TunCalc.SetExpression(const AStr: string);
begin
  FExpression := AStr;
  FDirty := True;
end;

procedure TunCalc.CreateDefaultVars;
begin
  CreateVar('PI', 3.14159265358979);
  CreateVar('X', 0.0);
  CreateVar('Y', 0.0);
end;

procedure TunCalc.CreateDefaultFuncs;
begin
  CreateNParamFunc('SQR', @_square, 1);
  CreateNParamFunc('SIN', @_sin, 1);
  CreateNParamFunc('COS', @_cos, 1);
  CreateNParamFunc('ATAN', @_arctan, 1);
  CreateNParamFunc('SINH', @_sinh, 1);
  CreateNParamFunc('COSH', @_cosh, 1);
  CreateNParamFunc('COTAN', @_cotan, 1);
  CreateNParamFunc('TAN', @_tan, 1);
  CreateNParamFunc('EXP', @_exp, 1);
  CreateNParamFunc('LN', @_ln, 1);
  CreateNParamFunc('LOG', @_log10, 1);
  CreateNParamFunc('SQRT', @_sqrt, 1);
  CreateNParamFunc('ABS', @_abs, 1);
  CreateNParamFunc('SIGN', @_sign, 1);
  CreateNParamFunc('TRUNC', @_trunc, 1);
  CreateNParamFunc('CEIL', @_ceil, 1);
  CreateNParamFunc('FLOOR', @_floor, 1);
  CreateNParamFunc('RND', @_rnd, 1);
  CreateNParamFunc('RANDOM', @_random, 1);
  CreateNParamFunc('INTPOW', @_intpower, 2);
  CreateNParamFunc('POW', @_power, 2);
  CreateNParamFunc('LOGN', @_logn, 2);
  CreateNParamFunc('MIN', @_min, 2);
  CreateNParamFunc('MAX', @_max, 2);
  CreateNParamFunc('MOD', @_modulo, 2);
  CreateNParamFunc('IF', @_if, 3);
  CreateNParamFunc('SUM', @_sum, -1);
end;

procedure TunCalc.DeleteAllVars;
var
  pValue: PEXTENDED;
begin
  if FVariables.Count > 0 then
  begin
    for pValue in FVariables.Values do
    begin
      Dispose(pValue);
    end;
    FVariables.Clear;
    FDirty := True;
  end;
end;

procedure TunCalc.DeleteAllFuncs;
var
  pValue: PNParamFuncRecord;
begin
  for pValue in FNParFuncs.Values do
  begin
    Dispose(pValue);
  end;
  FNParFuncs.Clear;
  FDirty := True;
end;

function TunCalc.GetFunctions: TStringList;
var
  FuncList: TStringList;
  Key: string;
begin
  FuncList := TStringList.Create;
  for Key in FNParFuncs.Keys do
    FuncList.Add(Key);
  Result := FuncList;
end;

function TunCalc.GetVariables: TStringList;
var
  VarList: TStringList;
  Key: string;
begin
  VarList := TStringList.Create;
  for Key in FVariables.Keys do
    VarList.Add(Key);
  Result := VarList;
end;

function TunCalc.GetVariablesUsed: TStringList;
var
  slVarList, slDefinedVarList: TStringList;
  i, Len: Integer;
  Temp: string;
begin
  if (FDirty) and (Length(FExpression)>0) then
    Parse();
  slVarList := TStringList.Create;
  if FNode <> nil then
  begin
    slDefinedVarList := GetVariables();
    Len := slDefinedVarList.Count-1;
    for i := 0 to Len do
    begin
      Temp := slDefinedVarList.strings[i];
      if IsVariableUsed(Temp) then
        slVarList.Add(Temp);
    end;
    FindVariablesUsed(FNode, slVarList);
  end;
  Result := slVarList;
end;

procedure TunCalc.SetX(const x: extended);
begin
  AssignVar('X', x);
end;

function TunCalc.GetX;
begin
  Result := GetVar('X');
end;

procedure TunCalc.SetY(const y: extended);
begin
  AssignVar('Y', y);
end;

function TunCalc.GetY;
begin
  Result := GetVar('Y');
end;

function TunCalc.IsVariable(const AVarName: string): Boolean;
begin
  if FVariables.ContainsKey(UpperCase(AVarName)) then
    Result := True
  else
   Result := False;
end;

function TunCalc.IsNParamFunction(const AFuncName: string): Boolean;
begin
  if FNParFuncs.ContainsKey(UpperCase(AFuncName)) then
      Result := True
  else
     Result := False;
end;

function TunCalc.IsFunction(const AFuncName: string): Boolean;
begin
  Result := IsNParamFunction(UpperCase(AFuncName));
end;

procedure TunCalc.FreeParseTree;
begin
  FNode.Free;
  FNode := nil;
  FDirty := True; //if Dirty next time we call Evaluate, it will call the Parse method.
end;

function TunCalc.IsVariableUsed(const AVarName: string): Boolean;
var
  pVarAddr: PEXTENDED;
  UpcName: string;
begin
  //we might exit this function as a result of exception at this moment
  Parse; //creating parse tree if it is not created yet.
  pVarAddr := nil;
  UpcName := UpperCase(AVarName);
  if FVariables.TryGetValue(UpcName, pVarAddr) then
    Result := FNode.IsUsed(pVarAddr)
  else if Assigned(OnVariableFound) then
  begin
    VariableToSearchFor := UpcName;
    Result := FNode.IsUsed(nil);
    VariableToSearchFor := '';
  end
  else Result := False;
end;

function TunCalc.IsFunctionUsed(const AFuncName: string): Boolean;
var
  PFuncRecord: PNParamFuncRecord;
  sUpcName: string;
begin
  //we might exit this function as a result of exception at this moment
  Parse; //creating parse tree if it is not created yet.
  sUpcName := UpperCase(AFuncName);
   if FNParFuncs.TryGetValue(sUpcName, PFuncRecord) then //to use TStringList.Find the list must be sorted.
      Result := FNode.IsUsed(@PFuncRecord^.Func)
   else Result := False;
end;

procedure TunCalc.Optimize;
begin
  OptimizeNode(FNode);
end;

procedure TunCalc.Randomize;
begin
  System.Randomize;
end;

end.
