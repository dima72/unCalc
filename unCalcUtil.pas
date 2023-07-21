unit unCalcUtil;
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

{$ZEROBASEDSTRINGS ON}

interface
  uses System.Math, SysUtils, Generics.Collections;
const
  MAX_NAME_LEN = 10;

type
  PEXTENDED = ^extended;

type
  EunCalcError = class(Exception)
  private
    FExp : string; //An expression that caused an error.
    FErr : string; //Error-causing portion of an expression.
  public
    constructor Create(const AMsg : string; const AErrPortion : string; const AExp : string);
    function GetInvalidPortionOfExpression: string; virtual;
    function GetSubExpression: string; virtual;
  end; //Defining a new exception class

  function _greater(const x: array of extended): extended;
  function _less(const x: array of extended): extended;
  function _equal(const x: array of extended): extended;
  function _ltequals(const x: array of extended): extended;
  function _gtequals(const x: array of extended): extended;
  function _notequals(const x: array of extended): extended;
  function _and(const x: array of extended): extended;
  function _or(const x: array of extended): extended;
  function _not(const x: array of extended): extended;
  function _unaryadd(const x: array of extended): extended;
  function _add(const x: array of extended): extended;
  function _subtract(const x: array of extended): extended;
  function _multiply(const x: array of extended): extended;
  function _divide(const x: array of extended): extended;
  function _modulo(const x: array of extended): extended;
  function _intdiv(const x: array of extended): extended;
  function _negate(const x: array of extended): extended;
  function _intpower(const x: array of extended): extended;
  function _square(const x: array of extended): extended;
  function _power(const x: array of extended): extended;
  function _sin(const x: array of extended): extended;
  function _cos(const x: array of extended): extended;
  function _arctan(const x: array of extended): extended;
  function _sinh(const x: array of extended): extended;
  function _cosh(const x: array of extended): extended;
  function _cotan(const x: array of extended): extended;
  function _tan(const x: array of extended): extended;
  function _exp(const x: array of extended): extended;
  function _ln(const x: array of extended): extended;
  function _log10(const x: array of extended): extended;
  function _logN(const x: array of extended): extended;
  function _sqrt(const x: array of extended): extended;
  function _abs(const x: array of extended): extended;
  function _min(const x: array of extended): extended;
  function _max(const x: array of extended): extended;
  function _sign(const x: array of extended): extended;
  function _trunc(const x: array of extended): extended;
  function _ceil(const x: array of extended): extended;
  function _floor(const x: array of extended): extended;
  function _rnd(const x: array of extended): extended;
  function _random(const x: array of extended): extended;
  function _if(const x: array of extended): extended;
  function _sum(const x: array of extended): extended;

  function IsValidChar(index : Integer; c : char): Boolean;
  function IsValidName(const AName : string): Boolean;
  function CheckBrackets(const AFormula : string) : Integer;
  function RemoveOuterBrackets(var AFormula: string): Boolean; //removes outer brackets in AFormula
  function IsValidNumber(const AFormula: string; var Number: extended): Boolean;
  procedure CheckError(AYes: Boolean; const AMsg: string; const AErrPortion: string; const AExp: string);

implementation

procedure CheckError(AYes: Boolean; const AMsg: string; const AErrPortion: string; const AExp: string);
begin
  if not AYes then
    raise EunCalcError.Create(AMsg, AErrPortion, AExp);
end;

constructor EunCalcError.Create(const AMsg : string; const AErrPortion : string; const AExp : string);
begin
  inherited Create(AMsg);
  FExp := AExp;
  Ferr := AErrPortion;
end;

function EunCalcError.GetInvalidPortionOfExpression: string;
begin
  Result:= FErr;
end;

function EunCalcError.GetSubExpression: string;
begin
  Result:= FExp;
end;

//Default Functions
//Users can assign own functions
function _greater(const x: array of extended): extended;
begin
  if x[0] > x[1] then Result := 1
  else Result := 0;
end;

function _less(const x: array of extended): extended;
begin
  if x[0] < x[1] then Result := 1
  else Result := 0;
end;

function _equal(const x: array of extended): extended;
begin
  if x[0] = x[1] then Result := 1
  else Result := 0;
end;

function _ltequals(const x: array of extended): extended;
begin
  if x[0] <= x[1] then Result := 1
  else Result := 0;
end;

function _gtequals(const x: array of extended): extended;
begin
  if x[0] >= x[1] then Result := 1
  else Result := 0;
end;

function _notequals(const x: array of extended): extended;
begin
  if x[0] <> x[1] then Result := 1
  else Result := 0;
end;

function _and(const x: array of extended): extended;
begin
  if ((x[0] <> 0) and (x[1] <> 0)) then Result := 1
  else Result := 0;
end;

function _or(const x: array of extended): extended;
begin
  if ((x[0] <> 0) or (x[1] <>0)) then Result := 1
  else Result := 0;
end;

function _not(const x: array of extended): extended;
begin
  if (x[0] = 0) then Result := 1
  else Result := 0;
end;

function _unaryadd(const x: array of extended): extended;
begin
  Result := x[0];
end;

function _add(const x: array of extended): extended;
begin
  Result := x[0] + x[1];
end;

function _subtract(const x: array of extended): extended;
begin
  Result := x[0] - x[1];
end;

function _multiply(const x: array of extended): extended;
begin
  Result := x[0] * x[1];
end;

function _divide(const x: array of extended): extended;
begin
  Result := x[0] / x[1];
end;

function _modulo(const x: array of extended): extended;
begin
  Result := trunc(x[0]) mod trunc(x[1]);
end;

function _intdiv(const x: array of extended): extended;
begin
  Result := trunc(x[0]) div trunc(x[1]);
end;

function _negate(const x: array of extended): extended;
begin
  Result := -x[0];
end;

function _intpower(const x: array of extended): extended;
begin
  Result := IntPower(x[0], trunc(x[1]));
end;

function _square(const x: array of extended): extended;
begin
  Result := sqr(x[0]);
end;

function _power(const x: array of extended): extended;
begin
  Result := Power(x[0], x[1]);
end;

function _sin(const x: array of extended): extended;
begin
  Result := sin(x[0]);
end;

function _cos(const x: array of extended): extended;
begin
  Result := cos(x[0]);
end;

function _arctan(const x: array of extended): extended;
begin
  Result := arctan(x[0]);
end;

function _sinh(const x: array of extended): extended;
begin
  Result := (exp(x[0]) - exp(-x[0])) * 0.5;
end;

function _cosh(const x: array of extended): extended;
begin
  Result := (exp(x[0]) + exp(-x[0])) * 0.5;
end;

function _cotan(const x: array of extended): extended;
begin
  Result := cotan(x[0]);
end;

function _tan(const x: array of extended): extended;
begin
  Result := tan(x[0]);
end;

function _exp(const x: array of extended): extended;
begin
  Result := exp(x[0]);
end;

function _ln(const x: array of extended): extended;
begin
  Result := ln(x[0]);
end;

function _log10(const x: array of extended): extended;
begin
  Result := log10(x[0]);
end;

function _logN(const x: array of extended): extended;
begin
  Result := logN(x[0], x[1]);
end;

function _sqrt(const x: array of extended): extended;
begin
  Result := sqrt(x[0]);
end;

function _abs(const x: array of extended): extended;
begin
  Result := abs(x[0]);
end;

function _min(const x: array of extended): extended;
begin
  if x[0] < x[1] then
    Result := x[0]
  else
    Result := x[1];
end;

function _max(const x: array of extended): extended;
begin
  if x[0] > x[1] then
    Result := x[0]
  else
    Result := x[1];
end;

function _sign(const x: array of extended): extended;
begin
  if x[0] < 0 then
    Result := -1
  else if x[0] > 0 then
    Result := 1.0
  else
    Result := 0.0;
end;

function _trunc(const x: array of extended): extended;
begin
  Result := int(x[0]);
end;

function _ceil(const x: array of extended): extended;
begin
  if frac(x[0]) > 0 then
    Result := int(x[0] + 1)
  else
    Result := int(x[0]);
end;

function _floor(const x: array of extended): extended;
begin
  if frac(x[0]) < 0 then
    Result := int(x[0] - 1)
  else
    Result := int(x[0]);
end;

function _rnd(const x: array of extended): extended;
begin
   Result := int(Random * int(x[0]));
end;

function _random(const x: array of extended): extended;
begin
  Result := Random * x[0];
end;

function _if(const x: array of extended): extended;
begin
  if x[0]<>0 then
    Result := x[1]
  else
    Result := x[2];
end;

function _sum(const x: array of extended): extended;
var i, len, total : Integer;
begin
  total := 0;
  len := Length(x);
  for i := 0 to len-1 do
  begin
    Inc(total, floor(x[i]));
  end;
  Result := total;
end;

function RemoveOuterBrackets(var AFormula: string): Boolean; //removes outer brackets in AFormula
var
  Temp: string;
  Len, LastIndex: Integer;
begin
  Result := false;
  Temp := AFormula;
  Len := Length(Temp);
  LastIndex := Len - 1;
  while (Len > 2) and (Temp[0] = '(') and (Temp[LastIndex] = ')') do
  begin
    Temp := Temp.Substring(0+1, Len-2);
    Temp := Trim(Temp); //after copy, "(((2-x)*3) )" would become "((2-x)*3) "
    if CheckBrackets(Temp)= -1 then
    begin//if succeed then assign to the return value
      Result := true;
      AFormula := Temp;
    end;
    Len := Length(Temp);
    LastIndex := Len - 1;
  end;
end;

function IsValidNumber(const AFormula: string; var Number: extended): Boolean;
begin
  Result := TryStrToFloat(AFormula, Number);
end;

function IsValidChar(index: Integer; c: char):Boolean;
begin
  if (index = 1) then
  begin //if first index
    if ((c >= 'A') and (c <= 'Z')) or (c = '_') then
      Result := true
    else
      Result := false;
  end
  else
  begin
    if ((c >= 'A') and (c <= 'Z')) or ((c >= '0') and (c <= '9')) or (c = '_') then
      Result := true
    else
      Result := false;
  end;
end;

function IsValidName(const AName : string):Boolean;
var
  i, LastIndex: Integer;
begin
  LastIndex := Length(AName) - 1;
  if LastIndex >= 0 then
  begin
    for i:= 0 to LastIndex do
    begin
      if not IsValidChar(i, AName[i]) then
      begin
        Result := false;
        exit;
      end;
    end;
  end;
  Result := true;
end;

//if success Returns -1, else returns the index of the character of the problem.
function CheckBrackets(const AFormula : string) : Integer;
var
  i, n, LastIndex: Integer;
begin
  //checks that the order and number of brackets are correct
  //it will say OK for something like 1+()()
  Result := -1;
  n := 0;
  LastIndex := Length(AFormula) - 1;
  if LastIndex > -1 then
  begin
   for i := 0 to LastIndex do
   begin
     case AFormula[i] of
       '(':
         inc(n);
       ')':
         dec(n);
     end;
     if n < 0 then
     begin
       Result := i;
       exit; // expression is not valid if different count of ) (
     end;
   end;
  end;
  if n > 0 then
    Result := LastIndex;
end;

end.
