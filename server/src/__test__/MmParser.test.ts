import { DisjointVarMap } from '../mm/DisjointVarMap';
import { MmParser, MmParserErrorCode, MmParserWarningCode } from "../mm/MmParser";
import { ProvableStatement } from "../mm/ProvableStatement";
import { LabeledStatement } from "../mm/LabeledStatement";
import { AssertionStatement } from "../mm/AssertionStatement";
                                                                                                                                                import { doesDiagnosticsContain, rebuildOriginalStringFromTokens } from '../mm/Utils';
import { createMmParser, impbiiMmParser, opelcnMmParser, vexTheoryMmParser } from './GlobalForTest.test';
import { Diagnostic, DiagnosticSeverity } from 'vscode-languageserver';
import { TokensCreator } from '../mm/TokensCreator';
import { MmToken } from '../grammar/MmLexer';
import { TokenReader } from '../mm/TokenReader';
import * as path from 'path';
import { BlockStatement } from '../mm/BlockStatement';

test("Parsing two $f statements", () => {
    const parser: MmParser = new MmParser();
    const text = `\
$c wff $.
$v ph $.
$v ps $.
wph $f wff ph $.
wps $f wff ps $.
`;
    const tokensCreator: TokensCreator = new TokensCreator();
    const mmTokens: MmToken[] = tokensCreator.createTokensFromText(text);
    const tokenReader: TokenReader = new TokenReader(mmTokens);
    parser.Parse(tokenReader);
    expect(parser.outermostBlock.fHyps.length).toBe(2);
    expect(parser.outermostBlock.fHyps[0].Variable).toBe("ph");
    expect(parser.outermostBlock.fHyps[1].Variable).toBe("ps");
});

// a self-contained database containing exactly and only the axioms and theorems for ax-mp
// wi would not be needed for the theory, but we need it for the Proof Assistant (the grammar for wff is the least requirement)
const axmpTheory = '$c ( $. $c ) $. $c -> $. $c wff $. $c |- $. $v ph $. ' +
    '$v ps $. wph $f wff ph $. wps $f wff ps $.\n' +
    'wi $a wff ( ph -> ps ) $.\n' +
    '${ min $e |- ph $.  maj $e |- ( ph -> ps ) $. ax-mp $a |- ps $.  $}';

test("Parsing axmp", () => {
    const parser: MmParser = new MmParser();
    parser.ParseText(axmpTheory);
    expect(parser.diagnostics.length).toBe(0);
    expect(parser.labelToStatementMap.size).toBe(6);
    expect(parser.labelToNonSyntaxAssertionMap.size).toBe(1);
});

test("Test anatomy - expect success", () => {
    const parser: MmParser = createMmParser('anatomy.mm');
    expect(parser.diagnostics.length).toBe(0);
    expect(parser.labelToStatementMap.size).toBe(6);
});

test('Test anatomy-bad1 , expect error', () => {
    // metamath.exe's error follows:
    // ?Error on line 29 of file "anatomy-bad1.mm" at statement 8, label "wnew", type
    // "$p":
    // wnew $p wff ( s -> ( r -> p ) ) $= ws wr wp w2 ws $.
    //                                                ^^
    // After proof step 5 (the last step), the RPN stack contains 3 entries: "ws"
    // (step 1), "w2" (step 4), and  "ws" (step 5).  It should contain exactly one
    // entry.
    const parser: MmParser = createMmParser('anatomy-bad1.mm');
    // expect(parser.diagnostics.length).toBe(0);
    expect(parser.parseFailed).toBeTruthy();
    expect(doesDiagnosticsContain(parser.diagnostics,
        MmParserErrorCode.stackHasMoreThanOneItemAtEndOfProof)).toBeTruthy();
    // expect(doesDiagnosticsContain(parser.diagnostics,
    //     MmParserErrorCode.assertionProvenDoesntMatch)).toBeTruthy();
});

test("Test big-unfier ; expect success", () => {
    const parser: MmParser = createMmParser('big-unifier.mm');
    expect(parser.parseFailed).toBeFalsy();
    expect(parser.diagnostics.length).toBe(0);
    expect(parser.labelToStatementMap.size).toBe(25);
});

test("Test big-unfier-bad1 ; expect error", () => {
    // metamath.exe's error follows: (it also has further details)
    // ?Error on line 68 of file "big-unifier-bad1.mm" at statement 28, label
    // "theorem1", type "$p":
    //    FFZMPAFFZFPFQPFZFLRFFLNKMJAJNQPLAPGPMKBADCEOARLIH $.
    //                                                   ^
    // The hypotheses of statement "ax-mp" at proof step 82 cannot be unified.
    const parser: MmParser = createMmParser('big-unifier-bad1.mm');
    expect(parser.parseFailed).toBeTruthy();
    expect(doesDiagnosticsContain(parser.diagnostics,
        MmParserErrorCode.eHypDoesntMatchTheStackEntry)).toBeTruthy();
    expect(parser.diagnostics[0].range.start.line).toBe(63);
    expect(parser.diagnostics[0].range.end.character).toBe(9);

});

test("Test disjoint2-good ; expect success", () => {
    const parser: MmParser = createMmParser('disjoint2-good.mm');
    expect(parser.parseFailed).toBeFalsy();
    expect(parser.labelToStatementMap.size).toBe(8);
    const labeledStatement: AssertionStatement = <AssertionStatement>parser.labelToStatementMap.get('good');
    // const disjVars: DisjVars = labeledStatement.frame!.disjVars;
    const disjVars: DisjointVarMap = labeledStatement.frame!.disjVars;
    expect(disjVars.map.size).toBe(3);
    expect(disjVars.containsDjContraint('x', 'y')).toBeTruthy();
    expect(disjVars.containsDjContraint('x', 'z')).toBeTruthy();
    expect(disjVars.containsDjContraint('x', 'w')).toBeTruthy();
    expect(disjVars.containsDjContraint('y', 'z')).toBeTruthy();
    expect(disjVars.containsDjContraint('y', 'w')).toBeTruthy();
    expect(disjVars.containsDjContraint('z', 'w')).toBeTruthy();
    expect(disjVars.containsDjContraint('w', 'x')).toBeTruthy();
    expect(disjVars.containsDjContraint('z', 'z')).toBeFalsy();
    expect(disjVars.containsDjContraint('x', 'a')).toBeFalsy();


});

test("Test disjoint2-almostgood ; expect error", () => {
    // metamath.exe's error follows: (it also has further details)
    // ?Error on line 30 of file "disjoint2.mm" at statement 21, label "almostgood",
    // type "$p":
    // xf yf combo zf wf combo ax-1 $.
    //                         ^^^^
    // There is a disjoint variable ($d) violation at proof step 7.  Assertion "ax-1"
    // requires that variables "x" and "y" be disjoint.  But "x" was substituted with
    // "( x y )" and "y" was substituted with "( z w )".
    // Variables "x" and "z" do not have a disjoint variable requirement in the
    // assertion being proved, "almostgood".
    // Three similar messages are given for missing djsj var requirement for w,x for y,z and for w,y
    const parser: MmParser = createMmParser('disjoint2-almostgood.mm');
    expect(parser.parseFailed).toBeTruthy();
    // expect(parser.diagnostics.length).toBe(4);
    expect(parser.diagnostics.length).toBe(1);
    expect(doesDiagnosticsContain(parser.diagnostics,
        MmParserErrorCode.missingDjVarsStatement)).toBeTruthy();
});

test("Test vex.mm; expect disj vars for axext3", () => {
    const provableStatement: ProvableStatement = <ProvableStatement>vexTheoryMmParser.labelToStatementMap.get('axext3');
    // const disjVars: DisjVars = provableStatement.frame!.disjVars;
    // $d z x w $.  $d z y w $.
    const disjVars: DisjointVarMap = provableStatement.frame!.disjVars;
    expect(disjVars.map.size).toBe(3);
    expect(disjVars.containsDjContraint('z', 'x')).toBeTruthy();
    expect(disjVars.containsDjContraint('z', 'w')).toBeTruthy();   // w is not a mandatory var
    expect(disjVars.containsDjContraint('w', 'x')).toBeTruthy();
    expect(disjVars.containsDjContraint('z', 'y')).toBeTruthy();
    expect(disjVars.containsDjContraint('y', 'w')).toBeTruthy();
    expect(disjVars.containsDjContraint('x', 'z')).toBeTruthy();
    expect(disjVars.containsDjContraint('x', 'y')).toBeFalsy();

});


test("expect opelcnParser to be successfully parsed", () => {

    expect(opelcnMmParser.isParsingComplete).toBeTruthy();
    expect(opelcnMmParser.parseFailed).toBeFalsy();
});

test("expect comments to be properly assigned", () => {
    const theoryWithComments = '$c ( $. $c ) $. $c -> $. $c wff $. $c |- $. $v ph $. ' +
        '$v ps $. wph $f wff ph $. wps $f wff ps $.\n' +
        '$( If ` ph ` and ` ps ` are wff\'s, so is ` ( ph -> ps ) ` $) ' +
        'wi $a wff ( ph -> ps ) $.\n' +
        '$( Rule of Modus Ponens. Propositional\n' +
        'calculus. $)\n' +
        '${ min $e |- ph $.  maj $e |- ( ph -> ps ) $. ax-mp $a |- ps $.  $}';

    const parser: MmParser = new MmParser();
    parser.ParseText(theoryWithComments);
    expect(parser.diagnostics.length).toBe(0);
    expect(parser.labelToStatementMap.size).toBe(6);
    const wi: LabeledStatement = parser.labelToStatementMap.get('wi')!;
    const wiCommentString = rebuildOriginalStringFromTokens(wi.comment!);
    //TODO try to understand why the following line produces a space before If, while in the last expect statement below,
    // there is no space before Rule
    expect(wiCommentString).toEqual(' If ` ph ` and ` ps ` are wff\'s, so is ` ( ph -> ps ) `');
    const axmp: LabeledStatement = parser.labelToStatementMap.get('ax-mp')!;
    const axmpCommentString = rebuildOriginalStringFromTokens(axmp.comment!);
    expect(axmpCommentString).toEqual('Rule of Modus Ponens. Propositional\ncalculus.');
});

test("expect mp2 ok", () => {
    const theory = '$c ( $. $c ) $. $c -> $. $c wff $. $c |- $. $v ph $.\n' +
        '$v ps $. $v ch $. wph $f wff ph $. wps $f wff ps $. wch $f wff ch $.\n' +
        '$( If ` ph ` and ` ps ` are wff\'s, so is ` ( ph -> ps ) ` $)\n' +
        'wi $a wff ( ph -> ps ) $.\n' +
        '${ min $e |- ph $.  maj $e |- ( ph -> ps ) $. ax-mp $a |- ps $.  $}\n' +
        '${ mp2.1 $e |- ph $. mp2.2 $e |- ps $. mp2.3 $e |- ( ph -> ( ps -> ch ) ) $.\n' +
        'mp2 $p |- ch $=\n' +
        '( wi ax-mp ) BCEABCGDFHH $.\n' +
        '$}\n';
    const parser: MmParser = new MmParser();
    parser.ParseText(theory);
    expect(parser.diagnostics.length).toBe(0);
});

test("expect missing close parenthesis in $p statement", () => {
    const theory = '$c ( $. $c ) $. $c -> $. $c wff $. $c |- $. $v ph $.\n' +
        '$v ps $. $v ch $. wph $f wff ph $. wps $f wff ps $. wch $f wff ch $.\n' +
        '$( If ` ph ` and ` ps ` are wff\'s, so is ` ( ph -> ps ) ` $)\n' +
        'wi $a wff ( ph -> ps ) $.\n' +
        '${ min $e |- ph $.  maj $e |- ( ph -> ps ) $. ax-mp $a |- ps $.  $}\n' +
        '${ mp2.1 $e |- ph $. mp2.2 $e |- ps $. mp2.3 $e |- ( ph -> ( ps -> ch ) ) $.\n' +
        'mp2 $p |- ch $=\n' +
        '( wi ax-mp )BCEABCGDFHH $.\n' +
        '$}\n';
    const parser: MmParser = new MmParser();
    parser.ParseText(theory);
    expect(parser.diagnostics.length).toBe(1);
    const diagnostic: Diagnostic = parser.diagnostics[0];
    expect(diagnostic.code).toBe(MmParserErrorCode.missingCloseParenthesisInPStatement);
    expect(diagnostic.message).toBe("Theorem mp2 : The $p statement mp2 does not contain a ')' token");
    expect(diagnostic.range.start.line).toBe(7);
    expect(diagnostic.range.start.character).toBe(11);
    expect(diagnostic.range.end.line).toBe(7);
    expect(diagnostic.range.end.character).toBe(23);
});

test("expect not a label of an assertion or optional hypothesis", () => {
    const theory = '$c ( $. $c ) $. $c -> $. $c wff $. $c |- $. $v ph $.\n' +
        '$v ps $. $v ch $. wph $f wff ph $. wps $f wff ps $. wch $f wff ch $.\n' +
        '$( If ` ph ` and ` ps ` are wff\'s, so is ` ( ph -> ps ) ` $)\n' +
        'wi $a wff ( ph -> ps ) $.\n' +
        '${ min $e |- ph $.  maj $e |- ( ph -> ps ) $. ax-mp $a |- ps $.  $}\n' +
        '${ mp2.1 $e |- ph $. mp2.2 $e |- ps $. mp2.3 $e |- ( ph -> ( ps -> ch ) ) $.\n' +
        'mp2 $p |- ch $=\n' +
        '( wixxx ax-mp ) BCEABCGDFHH $.\n' +
        '$}\n';
    const parser: MmParser = new MmParser();
    parser.ParseText(theory);
    expect(parser.diagnostics.length).toBeGreaterThanOrEqual(1);
    const diagnostic: Diagnostic = parser.diagnostics[0];
    expect(diagnostic.code).toBe(MmParserErrorCode.notALabelOfAssertionOrOptionalHyp);
    expect(diagnostic.message).toBe(
        "Theorem mp2 : 'wixxx' is not the label of an assertion or optional hypothesis");
    expect(diagnostic.range.start.line).toBe(7);
    expect(diagnostic.range.start.character).toBe(2);
    expect(diagnostic.range.end.line).toBe(7);
    expect(diagnostic.range.end.character).toBe(7);
});

// Test impbii-bad , expect error for con3d, but pm3.2im, that comes later and does not depend on con3d,
// should be added to the theory. con3rr3 depends on con3d and should have a diagnostic
test('Test impbii-bad , see comment above', () => {
    const parser: MmParser = createMmParser('impbii-bad.mm');
    expect(parser.parseFailed).toBeTruthy();
    const labelToStatementMap: Map<string, LabeledStatement> = parser.labelToStatementMap;
    expect(labelToStatementMap.size).toBeGreaterThan(0);
    const con1i: LabeledStatement | undefined = labelToStatementMap.get('con1i');
    expect(con1i).toBeDefined();
    expect((<ProvableStatement>con1i).isProofVerified).toBeTruthy();
    expect((<ProvableStatement>con1i).isProofVerificationFailed).toBeFalsy();
    const con3d: LabeledStatement | undefined = labelToStatementMap.get('con3d');
    expect(con3d).toBeDefined();
    expect((<ProvableStatement>con3d).isProofVerified).toBeFalsy();
    expect((<ProvableStatement>con3d).isProofVerificationFailed).toBeTruthy();
    const pm32im: LabeledStatement | undefined = labelToStatementMap.get('pm3.2im');
    expect(pm32im).toBeDefined();
    expect((<ProvableStatement>pm32im).isProofVerified).toBeTruthy();
    expect((<ProvableStatement>pm32im).isProofVerificationFailed).toBeFalsy();
    const con3rr3: LabeledStatement | undefined = labelToStatementMap.get('con3rr3');
    expect(con3rr3).toBeDefined();
    expect((<ProvableStatement>con3rr3).isProofVerified).toBeFalsy();
    expect((<ProvableStatement>con3rr3).isProofVerificationFailed).toBeTruthy();
    const impbi: LabeledStatement | undefined = labelToStatementMap.get('impbi');
    expect(impbi).toBeDefined();
    expect((<ProvableStatement>impbi).isProofVerified).toBeFalsy();
    expect((<ProvableStatement>impbi).isProofVerificationFailed).toBeTruthy();
    expect(parser.diagnostics.length).toBe(6);
    expect(parser.diagnostics[0].provableStatementLabel).toBe('con3d');
    expect(parser.diagnostics[0].code).toBe(MmParserErrorCode.eHypDoesntMatchTheStackEntry);
    expect(parser.diagnostics[1].provableStatementLabel).toBe('con3rr3');
    expect(parser.diagnostics[1].code).toBe(MmParserErrorCode.labelOfAProvableStatementWithFailedVerification);
    expect(parser.diagnostics[1].range.start.line).toBe(248);
    expect(parser.diagnostics[1].range.start.character).toBe(11);
    expect(parser.diagnostics[1].range.end.line).toBe(248);
    expect(parser.diagnostics[1].range.end.character).toBe(16);
    expect(parser.diagnostics[1].message).toBe(
        'Theorem con3rr3 : Provable statement con3d is in the theory, but its verification failed');
});

test("Test nested-frames ; expect success", () => {
    const parser: MmParser = createMmParser('nested-scopes.mm');
    expect(parser.parseFailed).toBeFalsy();
    expect(parser.labelToStatementMap.size).toBe(8);
    const labeledStatement: AssertionStatement = <AssertionStatement>parser.labelToStatementMap.get('good');
    // const disjVars: DisjVars = labeledStatement.frame!.disjVars;
    const disjVars: DisjointVarMap = labeledStatement.frame!.disjVars;
    expect(disjVars.map.size).toBe(3);
    expect(disjVars.containsDjContraint('x', 'y')).toBeTruthy();
    expect(disjVars.containsDjContraint('x', 'z')).toBeTruthy();
    expect(disjVars.containsDjContraint('x', 'w')).toBeTruthy();
    expect(disjVars.containsDjContraint('y', 'z')).toBeTruthy();  // this is the important one, for nested scopes
    expect(disjVars.containsDjContraint('y', 'w')).toBeTruthy();
    expect(disjVars.containsDjContraint('w', 'x')).toBeTruthy();
    expect(disjVars.containsDjContraint('z', 'z')).toBeFalsy();
    expect(disjVars.containsDjContraint('x', 'a')).toBeFalsy();
});

test("Test (New usage is discouraged.)", () => {
    const impbi: AssertionStatement = <AssertionStatement>impbiiMmParser.labelToStatementMap.get('impbi');
    const isImpbiDiscouraged: boolean = impbi.isDiscouraged;
    expect(isImpbiDiscouraged).toBeFalsy();

    const simprim: AssertionStatement = <AssertionStatement>impbiiMmParser.labelToStatementMap.get('notnotr');
    const isSimprimDiscouraged: boolean = simprim.isDiscouraged;
    expect(isSimprimDiscouraged).toBeTruthy();

    const id: AssertionStatement = <AssertionStatement>impbiiMmParser.labelToStatementMap.get('id');
    const isIdDiscouraged: boolean = id.isDiscouraged;
    expect(isIdDiscouraged).toBeFalsy();
});

// Test questionmark
// expect warning missing proof for a21
// for the time being, we don't emit warnings for other theorems that depend on a theorem with missing proof
test('Test questionmark , see comment above', () => {
    const parser: MmParser = createMmParser('questionmark.mm');
    expect(parser.parseFailed).toBeFalsy();
    const labelToStatementMap: Map<string, LabeledStatement> = parser.labelToStatementMap;
    expect(labelToStatementMap.size).toBeGreaterThan(0);
    const a1i: LabeledStatement | undefined = labelToStatementMap.get('a1i');
    expect(a1i).toBeDefined();
    expect((<ProvableStatement>a1i).isProofVerified).toBeTruthy();
    expect((<ProvableStatement>a1i).isProofVerificationFailed).toBeFalsy();
    const a2i: LabeledStatement | undefined = labelToStatementMap.get('a2i');
    expect(a2i).toBeDefined();
    expect((<ProvableStatement>a2i).isProofVerified).toBeFalsy();
    expect((<ProvableStatement>a2i).isProofVerificationFailed).toBeFalsy();
    const mpd: LabeledStatement | undefined = labelToStatementMap.get('mpd');
    expect(mpd).toBeDefined();
    expect((<ProvableStatement>mpd).isProofVerified).toBeTruthy();
    expect((<ProvableStatement>mpd).isProofVerificationFailed).toBeFalsy();
    const syl: LabeledStatement | undefined = labelToStatementMap.get('syl');
    expect(syl).toBeDefined();
    expect((<ProvableStatement>syl).isProofVerified).toBeTruthy();
    expect((<ProvableStatement>syl).isProofVerificationFailed).toBeFalsy();
    expect(parser.diagnostics.length).toBe(1);
    expect(parser.diagnostics[0].provableStatementLabel).toBe('a2i');
    expect(parser.diagnostics[0].severity).toBe(DiagnosticSeverity.Warning);
    expect(parser.diagnostics[0].code).toBe(MmParserWarningCode.unprovenStatement);
    expect(parser.diagnostics[0].message).toBe("Unproven $p statement");
    expect(parser.diagnostics[0].mmFilePath).toContain(path.normalize('server/src/__test__/../mmTestFiles/questionmark.mm'));
});

test('Test file inclusion', () => {
    const parser: MmParser = createMmParser('include.mm');
    expect(parser.parseFailed).toBeFalsy();
    const labelToStatementMap: Map<string, LabeledStatement> = parser.labelToStatementMap;
    expect(labelToStatementMap.size).toBeGreaterThan(0);
    const a1i: LabeledStatement | undefined = labelToStatementMap.get('a1i');
    expect(a1i).toBeDefined();
    expect((<ProvableStatement>a1i).isProofVerified).toBeTruthy();
    expect((<ProvableStatement>a1i).isProofVerificationFailed).toBeFalsy();
    const a2i: LabeledStatement | undefined = labelToStatementMap.get('a2i');
    expect(a2i).toBeDefined();
    expect((<ProvableStatement>a2i).isProofVerified).toBeFalsy();
    expect((<ProvableStatement>a2i).isProofVerificationFailed).toBeFalsy();
    const mpd: LabeledStatement | undefined = labelToStatementMap.get('mpd');
    expect(mpd).toBeDefined();
    expect((<ProvableStatement>mpd).isProofVerified).toBeTruthy();
    expect((<ProvableStatement>mpd).isProofVerificationFailed).toBeFalsy();
    const syl: LabeledStatement | undefined = labelToStatementMap.get('syl');
    expect(syl).toBeDefined();
    expect((<ProvableStatement>syl).isProofVerified).toBeTruthy();
    expect((<ProvableStatement>syl).isProofVerificationFailed).toBeFalsy();
    expect(parser.diagnostics.length).toBe(1);
    expect(parser.diagnostics[0].provableStatementLabel).toBe('a2i');
    expect(parser.diagnostics[0].code).toBe(MmParserWarningCode.unprovenStatement);
    expect(parser.diagnostics[0].mmFilePath).toContain(path.normalize('server/src/__test__/../mmTestFiles/included2.mm'));
});

test('buildLabelToStatementMap emits newLabel event when it finds a label', () => {
    class TestParser extends MmParser {
        buildLabelToStatementMap(toks: TokenReader, currentBlock?: BlockStatement): void {
            super.buildLabelToStatementMap(toks, currentBlock);
        }
    }

    const mmParser = new TestParser();

    mmParser.emit = jest.fn();

    const mockTokenReader = {
        indexForNextToken: 0,
        tokens: {length: 1},
        Readc: jest.fn().mockImplementation(() => {
            if (mockTokenReader.indexForNextToken === 0) {
                mockTokenReader.indexForNextToken = 6;
                return {value: 'myLabel'};
            } else {
                return undefined;
            }
        }) as () => MmToken
    } as TokenReader;

    mmParser.buildLabelToStatementMap(mockTokenReader);

    expect(mmParser.emit).toBeCalledTimes(1);
    expect(mmParser.emit).toBeCalledWith('newLabel', {value: 'myLabel'});
});
