import { TextEdit } from 'vscode-languageserver-textdocument';
import { ProofMode, DisjVarAutomaticGeneration } from '../mm/ConfigurationManager';
import { MmParser } from '../mm/MmParser';
import { IMmpParserParams, MmpParser } from '../mmp/MmpParser';
import { MmpProofStep } from "../mmp/MmpProofStep";
import { MmpUnifier } from '../mmp/MmpUnifier';
import { WorkingVars } from '../mmp/WorkingVars';
import { eqeq1iMmParser, impbiiMmParser, kindToPrefixMap, mp2MmParser, mp2Theory, opelcnMmParser, vexTheoryMmParser } from './GlobalForTest.test';

test('buildNewProof()', () => {
	const mmpSource = `
* test comment

ax-mp
qed:: |- ps`;
	// const parser: MmParser = new MmParser();
	// parser.ParseText(axmpTheory);
	const mmpParserParams: IMmpParserParams = {
		textToParse: mmpSource,
		mmParser: mp2MmParser,
		workingVars: new WorkingVars(kindToPrefixMap)
	};
	const mmpParser: MmpParser = new MmpParser(mmpParserParams);
	// const mmpParser: MmpParser = new MmpParser(mmpSource, mp2MmParser, new WorkingVars(kindToPrefixMap));
	mmpParser.parse();
	const mmpUnifier: MmpUnifier = new MmpUnifier(
		{
			mmpParser: mmpParser,
			proofMode: ProofMode.normal,
			maxNumberOfHypothesisDispositionsForStepDerivation: 0,
			renumber: false,
			removeUnusedStatements: false
		});
	expect(mmpUnifier.uProof!.mmpStatements.length).toBe(3);
	expect((<MmpProofStep>mmpUnifier.uProof!.mmpStatements[1]).stepLabel).toEqual('ax-mp');
});

test('Unify ax-mp', () => {
	const mmpSource = `
* test comment

ax-mp
qed:: |- ps`;
	// const parser: MmParser = new MmParser();
	// parser.ParseText(axmpTheory);
	const mmpParserParams: IMmpParserParams = {
		textToParse: mmpSource,
		mmParser: opelcnMmParser,
		workingVars: new WorkingVars(kindToPrefixMap)
	};
	const mmpParser: MmpParser = new MmpParser(mmpParserParams);
	// const mmpParser: MmpParser = new MmpParser(mmpSource, mp2MmParser, new WorkingVars(kindToPrefixMap));
	mmpParser.parse();
	const mmpUnifier: MmpUnifier = new MmpUnifier(
		{
			mmpParser: mmpParser,
			proofMode: ProofMode.normal,
			maxNumberOfHypothesisDispositionsForStepDerivation: 0,
			renumber: false,
			removeUnusedStatements: false
		});
	mmpUnifier.unify();
	const textEditArray: TextEdit[] = mmpUnifier.textEditArray;
	expect(textEditArray.length).toBe(1);
	const newTextExpected = `
* test comment

d2::                |- &W1
d3::                |- ( &W1 -> &W2 )
d1:d2,d3:ax-mp     |- &W2
qed::              |- ps
`;
	const textEdit: TextEdit = textEditArray[0];
	expect(textEdit.newText).toEqual(newTextExpected);
});

test('Unify 2 ax-mp', () => {
	const mmpSource = `
* test comment

qed::ax-mp |- ph`;
	// const parser: MmParser = new MmParser();
	// parser.ParseText(axmpTheory);
	const mmpParserParams: IMmpParserParams = {
		textToParse: mmpSource,
		mmParser: mp2MmParser,
		workingVars: new WorkingVars(kindToPrefixMap)
	};
	const mmpParser: MmpParser = new MmpParser(mmpParserParams);
	// const mmpParser: MmpParser = new MmpParser(mmpSource, mp2MmParser, new WorkingVars(kindToPrefixMap));
	mmpParser.parse();
	const mmpUnifier: MmpUnifier = new MmpUnifier(
		{
			mmpParser: mmpParser,
			proofMode: ProofMode.normal,
			maxNumberOfHypothesisDispositionsForStepDerivation: 0,
			renumber: false,
			removeUnusedStatements: false
		});
	mmpUnifier.unify();
	const textEditArray: TextEdit[] = mmpUnifier.textEditArray;
	expect(textEditArray.length).toBe(1);
	const newTextExpected = `
* test comment

d1::                |- &W1
d2::                |- ( &W1 -> ph )
qed:d1,d2:ax-mp    |- ph
`;
	const textEdit: TextEdit = textEditArray[0];
	expect(textEdit.newText).toEqual(newTextExpected);
});

test('Unify 3 ax-mp', () => {
	const mmpSource = `
* test comment

50:: |- ( &W3 -> ph )
qed:,50:ax-mp |- ph`;
	// const parser: MmParser = new MmParser();
	// parser.ParseText(axmpTheory);
	const mmpParserParams: IMmpParserParams = {
		textToParse: mmpSource,
		mmParser: mp2MmParser,
		workingVars: new WorkingVars(kindToPrefixMap)
	};
	const mmpParser: MmpParser = new MmpParser(mmpParserParams);
	// const mmpParser: MmpParser = new MmpParser(mmpSource, mp2MmParser, new WorkingVars(kindToPrefixMap));
	mmpParser.parse();
	const mmpUnifier: MmpUnifier = new MmpUnifier(
		{
			mmpParser: mmpParser, proofMode: ProofMode.normal,
			maxNumberOfHypothesisDispositionsForStepDerivation: 0,
			renumber: false,
			removeUnusedStatements: false
		});
	mmpUnifier.unify();
	const textEditArray: TextEdit[] = mmpUnifier.textEditArray;
	expect(textEditArray.length).toBe(1);
	const newTextExpected = `
* test comment

50::                |- ( &W3 -> ph )
d1::                |- &W3
qed:d1,50:ax-mp    |- ph
`;
	const textEdit: TextEdit = textEditArray[0];
	expect(textEdit.newText).toEqual(newTextExpected);
});

test('Unify with working var ax-mp', () => {
	const mmpSource = `
* test comment

h1::a |- ps
h2::b |- &W1
5:1,2:ax-mp |- ph
qed::d |- ps
`;
	// const parser: MmParser = new MmParser();
	// parser.ParseText(axmpTheory);
	const mmpParserParams: IMmpParserParams = {
		textToParse: mmpSource,
		mmParser: mp2MmParser,
		workingVars: new WorkingVars(kindToPrefixMap)
	};
	const mmpParser: MmpParser = new MmpParser(mmpParserParams);
	// const mmpParser: MmpParser = new MmpParser(mmpSource, mp2MmParser, new WorkingVars(kindToPrefixMap));
	mmpParser.parse();
	const mmpUnifier: MmpUnifier = new MmpUnifier(
		{
			mmpParser: mmpParser, proofMode: ProofMode.normal,
			maxNumberOfHypothesisDispositionsForStepDerivation: 0,
			renumber: false,
			removeUnusedStatements: false
		});
	mmpUnifier.unify();
	const textEditArray: TextEdit[] = mmpUnifier.textEditArray;
	expect(textEditArray.length).toBe(1);
	const newTextExpected = `
* test comment

h1::a               |- ps
h2::b               |- ( ps -> ph )
5:1,2:ax-mp        |- ph
qed::d             |- ps
`;
	const textEdit: TextEdit = textEditArray[0];
	expect(textEdit.newText).toEqual(newTextExpected);
});

test('Unify double ax-mp', () => {
	const mmpSource = `
* test comment

50:ax-mp
qed:,50:ax-mp |- ph`;
	// const parser: MmParser = new MmParser();
	// parser.ParseText(axmpTheory);
	const mmpParserParams: IMmpParserParams = {
		textToParse: mmpSource,
		mmParser: mp2MmParser,
		workingVars: new WorkingVars(kindToPrefixMap)
	};
	const mmpParser: MmpParser = new MmpParser(mmpParserParams);
	// const mmpParser: MmpParser = new MmpParser(mmpSource, mp2MmParser, new WorkingVars(kindToPrefixMap));
	mmpParser.parse();
	const mmpUnifier: MmpUnifier = new MmpUnifier(
		{
			mmpParser: mmpParser, proofMode: ProofMode.normal,
			maxNumberOfHypothesisDispositionsForStepDerivation: 0,
			renumber: false,
			removeUnusedStatements: false
		});
	mmpUnifier.unify();
	const textEditArray: TextEdit[] = mmpUnifier.textEditArray;
	expect(textEditArray.length).toBe(1);
	const newTextExpected = `
* test comment

d1::                 |- &W1
d2::                 |- ( &W1 -> ( &W3 -> ph ) )
50:d1,d2:ax-mp      |- ( &W3 -> ph )
d3::                |- &W3
qed:d3,50:ax-mp    |- ph
`;
	const textEdit: TextEdit = textEditArray[0];
	expect(textEdit.newText).toEqual(newTextExpected);
});

test('Expect new ref to be d7', () => {
	const mmpSource = `
* test comment
d6:: |- ( ps -> ph )
qed:,d6:ax-mp    |- ph
`;
	// const parser: MmParser = new MmParser();
	// parser.ParseText(axmpTheory);
	const mmpParserParams: IMmpParserParams = {
		textToParse: mmpSource,
		mmParser: mp2MmParser,
		workingVars: new WorkingVars(kindToPrefixMap)
	};
	const mmpParser: MmpParser = new MmpParser(mmpParserParams);
	// const mmpParser: MmpParser = new MmpParser(mmpSource, mp2MmParser, new WorkingVars(kindToPrefixMap));
	mmpParser.parse();
	const mmpUnifier: MmpUnifier = new MmpUnifier(
		{
			mmpParser: mmpParser, proofMode: ProofMode.normal,
			maxNumberOfHypothesisDispositionsForStepDerivation: 0,
			renumber: false,
			removeUnusedStatements: false
		});
	mmpUnifier.unify();
	const adjustedIndex: number | undefined = mmpUnifier.uProof?.adjustedStepIndexForThisFormula('|- ph');
	expect(adjustedIndex).toBe(3);
	const textEditArray: TextEdit[] = mmpUnifier.textEditArray;
	expect(textEditArray.length).toBe(1);
	const newTextExpected = `
* test comment

d6::                |- ( ps -> ph )
d7::                |- ps
qed:d7,d6:ax-mp    |- ph
`;
	const textEdit: TextEdit = textEditArray[0];
	expect(textEdit.newText).toEqual(newTextExpected);
});

test('Expect new working var to be &W4', () => {
	const mmpSource = `
* test comment

d1:: |- &W3
qed::ax-mp  |- ph`;
	// const parser: MmParser = new MmParser();
	// parser.ParseText(axmpTheory);
	const mmpParserParams: IMmpParserParams = {
		textToParse: mmpSource,
		mmParser: mp2MmParser,
		workingVars: new WorkingVars(kindToPrefixMap)
	};
	const mmpParser: MmpParser = new MmpParser(mmpParserParams);
	// const mmpParser: MmpParser = new MmpParser(mmpSource, mp2MmParser, new WorkingVars(kindToPrefixMap));
	mmpParser.parse();
	const mmpUnifier: MmpUnifier = new MmpUnifier(
		{
			mmpParser: mmpParser, proofMode: ProofMode.normal,
			maxNumberOfHypothesisDispositionsForStepDerivation: 0,
			renumber: false,
			removeUnusedStatements: false
		});
	mmpUnifier.unify();
	const textEditArray: TextEdit[] = mmpUnifier.textEditArray;
	expect(textEditArray.length).toBe(1);
	const newTextExpected = `
* test comment

d1::               |- &W3
d2::                |- &W4
d3::                |- ( &W4 -> ph )
qed:d2,d3:ax-mp    |- ph
`;
	const textEdit: TextEdit = textEditArray[0];
	expect(textEdit.newText).toEqual(newTextExpected);
});

test('Complete ax-mp', () => {
	const mmpSource = `
* test comment

qed:ax-mp |- ( ps -> ph )`;
	// const parser: MmParser = new MmParser();
	// parser.ParseText(axmpTheory);
	const mmpParserParams: IMmpParserParams = {
		textToParse: mmpSource,
		mmParser: mp2MmParser,
		workingVars: new WorkingVars(kindToPrefixMap)
	};
	const mmpParser: MmpParser = new MmpParser(mmpParserParams);
	// const mmpParser: MmpParser = new MmpParser(mmpSource, mp2MmParser, new WorkingVars(kindToPrefixMap));
	mmpParser.parse();
	const mmpUnifier: MmpUnifier = new MmpUnifier(
		{
			mmpParser: mmpParser, proofMode: ProofMode.normal,
			maxNumberOfHypothesisDispositionsForStepDerivation: 0,
			renumber: false,
			removeUnusedStatements: false
		});
	mmpUnifier.unify();
	const textEditArray: TextEdit[] = mmpUnifier.textEditArray;
	expect(textEditArray.length).toBe(1);
	const newTextExpected = `
* test comment

d1::                |- &W1
d2::                |- ( &W1 -> ( ps -> ph ) )
qed:d1,d2:ax-mp    |- ( ps -> ph )
`;
	const textEdit: TextEdit = textEditArray[0];
	expect(textEdit.newText).toEqual(newTextExpected);
});

test('Mgu inolving logical vars on the right side', () => {
	const mmpSource = `
* test comment

d1::              |- &W1
d2::              |- &W2
qed:d1,d2:ax-mp     |- ( ph -> ch )`;
	// const parser: MmParser = new MmParser();
	// parser.ParseText(axmpTheory);
	const mmpParserParams: IMmpParserParams = {
		textToParse: mmpSource,
		mmParser: mp2MmParser,
		workingVars: new WorkingVars(kindToPrefixMap)
	};
	const mmpParser: MmpParser = new MmpParser(mmpParserParams);
	// const mmpParser: MmpParser = new MmpParser(mmpSource, mp2MmParser, new WorkingVars(kindToPrefixMap));
	mmpParser.parse();
	const mmpUnifier: MmpUnifier = new MmpUnifier(
		{
			mmpParser: mmpParser, proofMode: ProofMode.normal,
			maxNumberOfHypothesisDispositionsForStepDerivation: 0,
			renumber: false,
			removeUnusedStatements: false
		});
	mmpUnifier.unify();
	const textEditArray: TextEdit[] = mmpUnifier.textEditArray;
	expect(textEditArray.length).toBe(1);
	const newTextExpected = `
* test comment

d1::                |- &W1
d2::                |- ( &W1 -> ( ph -> ch ) )
qed:d1,d2:ax-mp    |- ( ph -> ch )
`;
	const textEdit: TextEdit = textEditArray[0];
	expect(textEdit.newText).toEqual(newTextExpected);
});

test('Expect unify error to leave line unchanged', () => {
	const mmpSource = `
* test comment

ax-mp:: |- ( ch -> )
qed:: |- ps`;
	// const parser: MmParser = new MmParser();
	// parser.ParseText(axmpTheory);
	const mmpParserParams: IMmpParserParams = {
		textToParse: mmpSource,
		mmParser: mp2MmParser,
		workingVars: new WorkingVars(kindToPrefixMap)
	};
	const mmpParser: MmpParser = new MmpParser(mmpParserParams);
	// const mmpParser: MmpParser = new MmpParser(mmpSource, mp2MmParser, new WorkingVars(kindToPrefixMap));
	mmpParser.parse();
	const mmpUnifier: MmpUnifier = new MmpUnifier(
		{
			mmpParser: mmpParser, proofMode: ProofMode.normal,
			maxNumberOfHypothesisDispositionsForStepDerivation: 0,
			renumber: false,
			removeUnusedStatements: false
		});
	mmpUnifier.unify();
	const textEditArray: TextEdit[] = mmpUnifier.textEditArray;
	expect(textEditArray.length).toBe(1);
	const textEdit: TextEdit = textEditArray[0];
	const newTextExpected = `
* test comment

ax-mp::            |- ( ch -> )
qed::              |- ps
`;
	expect(textEdit.newText).toEqual(newTextExpected);
});

test('Expect 2 unify error to leave line unchanged', () => {
	// ZZ is unknown, thus formula is not parsed and the unification should do nothing
	const mmpSource = `
* test comment

qed::ax-mp |- M e. ZZ`;
	// const parser: MmParser = new MmParser();
	// parser.ParseText(axmpTheory);
	const mmpParserParams: IMmpParserParams = {
		textToParse: mmpSource,
		mmParser: mp2MmParser,
		workingVars: new WorkingVars(kindToPrefixMap)
	};
	const mmpParser: MmpParser = new MmpParser(mmpParserParams);
	// const mmpParser: MmpParser = new MmpParser(mmpSource, mp2MmParser, new WorkingVars(kindToPrefixMap));
	mmpParser.parse();
	const mmpUnifier: MmpUnifier = new MmpUnifier(
		{
			mmpParser: mmpParser, proofMode: ProofMode.normal,
			maxNumberOfHypothesisDispositionsForStepDerivation: 0,
			renumber: false,
			removeUnusedStatements: false
		});
	mmpUnifier.unify();
	const textEditArray: TextEdit[] = mmpUnifier.textEditArray;
	expect(textEditArray.length).toBe(1);
	const textEdit: TextEdit = textEditArray[0];
	const newTextExpected = `
* test comment

qed::ax-mp         |- M e. ZZ
`;
	expect(textEdit.newText).toEqual(newTextExpected);
});

test('Expect impbii ref error to leave line unchanged', () => {
	// we've decided not to remove the wrong ref
	const mmpSource = `
* test comment

qed:5:impbii |- ch`;
	const mmpParserParams: IMmpParserParams = {
		textToParse: mmpSource,
		mmParser: impbiiMmParser,
		workingVars: new WorkingVars(kindToPrefixMap)
	};
	const mmpParser: MmpParser = new MmpParser(mmpParserParams);
	// const mmpParser: MmpParser = new MmpParser(mmpSource, impbiiMmParser, new WorkingVars(kindToPrefixMap));
	mmpParser.parse();
	const mmpUnifier: MmpUnifier = new MmpUnifier(
		{
			mmpParser: mmpParser, proofMode: ProofMode.normal,
			maxNumberOfHypothesisDispositionsForStepDerivation: 0,
			renumber: false,
			removeUnusedStatements: false
		});
	mmpUnifier.unify();
	const textEditArray: TextEdit[] = mmpUnifier.textEditArray;
	expect(textEditArray.length).toBe(1);
	const textEdit: TextEdit = textEditArray[0];
	const newTextExpected = `
* test comment

qed:5:impbii       |- ch
`;
	expect(textEdit.newText).toEqual(newTextExpected);
});

test('Expect long label to move the formula to new line', () => {
	// we've decided not to remove the wrong ref
	const mmpSource = `
* test comment

qed::exactlonglabel |- ch`;
	const mmpParserParams: IMmpParserParams = {
		textToParse: mmpSource,
		mmParser: impbiiMmParser,
		workingVars: new WorkingVars(kindToPrefixMap)
	};
	const mmpParser: MmpParser = new MmpParser(mmpParserParams);
	// const mmpParser: MmpParser = new MmpParser(mmpSource, impbiiMmParser, new WorkingVars(kindToPrefixMap));
	mmpParser.parse();
	const mmpUnifier: MmpUnifier = new MmpUnifier(
		{
			mmpParser: mmpParser, proofMode: ProofMode.normal,
			maxNumberOfHypothesisDispositionsForStepDerivation: 0,
			renumber: false,
			removeUnusedStatements: false
		});
	mmpUnifier.unify();
	const textEditArray: TextEdit[] = mmpUnifier.textEditArray;
	expect(textEditArray.length).toBe(1);
	const textEdit: TextEdit = textEditArray[0];
	const newTextExpected = `
* test comment

qed::exactlonglabel
                   |- ch
`;
	expect(textEdit.newText).toEqual(newTextExpected);
});

test('Expect ref error to leave line unchanged', () => {
	// we've decided not to remove the wrong ref
	const mmpSource = `
* test comment

qed:5:ax-mp |- ch`;
	const parser: MmParser = new MmParser();
	parser.ParseText(mp2Theory);
	const mmpParserParams: IMmpParserParams = {
		textToParse: mmpSource,
		mmParser: parser,
		workingVars: new WorkingVars(kindToPrefixMap)
	};
	const mmpParser: MmpParser = new MmpParser(mmpParserParams);
	// const mmpParser: MmpParser = new MmpParser(mmpSource, parser, new WorkingVars(kindToPrefixMap));
	mmpParser.parse();
	const mmpUnifier: MmpUnifier = new MmpUnifier(
		{
			mmpParser: mmpParser, proofMode: ProofMode.normal,
			maxNumberOfHypothesisDispositionsForStepDerivation: 0,
			renumber: false,
			removeUnusedStatements: false
		});
	mmpUnifier.unify();
	const textEditArray: TextEdit[] = mmpUnifier.textEditArray;
	expect(textEditArray.length).toBe(1);
	const textEdit: TextEdit = textEditArray[0];
	const newTextExpected = `
* test comment

qed:5:ax-mp        |- ch
`;
	expect(textEdit.newText).toEqual(newTextExpected);
});

test('unify a1i with already present working var', () => {
	const mmpSource = `
* test comment

a::a1i |- &W1
qed:: |- ch`;
	// const impbiiMmParser: MmParser = new MmParser();
	// impbiiMmParser.ParseText(impbiiTheory);
	const mmpParserParams: IMmpParserParams = {
		textToParse: mmpSource,
		mmParser: impbiiMmParser,
		workingVars: new WorkingVars(kindToPrefixMap)
	};
	const mmpParser: MmpParser = new MmpParser(mmpParserParams);
	// const mmpParser: MmpParser = new MmpParser(mmpSource, impbiiMmParser, new WorkingVars(kindToPrefixMap));
	mmpParser.parse();
	const mmpUnifier: MmpUnifier = new MmpUnifier(
		{
			mmpParser: mmpParser, proofMode: ProofMode.normal,
			maxNumberOfHypothesisDispositionsForStepDerivation: 0,
			renumber: false,
			removeUnusedStatements: false
		});
	mmpUnifier.unify();
	const textEditArray: TextEdit[] = mmpUnifier.textEditArray;
	expect(textEditArray.length).toBe(1);
	const newTextExpected = `
* test comment

d1::                |- &W2
a:d1:a1i           |- ( &W3 -> &W2 )
qed::              |- ch
`;
	const textEdit: TextEdit = textEditArray[0];
	expect(textEdit.newText).toEqual(newTextExpected);
});

test('Expect comments to be left unchanged', () => {
	const mmpSource = `* comment that
  should be left on two lines, with   wierd     spacing preserved
6:: |- ps
* second comment    to be left    unchanged
qed:5:ax-mp |- ch`;
	const parser: MmParser = new MmParser();
	parser.ParseText(mp2Theory);
	const mmpParserParams: IMmpParserParams = {
		textToParse: mmpSource,
		mmParser: parser,
		workingVars: new WorkingVars(kindToPrefixMap)
	};
	const mmpParser: MmpParser = new MmpParser(mmpParserParams);
	// const mmpParser: MmpParser = new MmpParser(mmpSource, parser, new WorkingVars(kindToPrefixMap));
	mmpParser.parse();
	const mmpUnifier: MmpUnifier = new MmpUnifier(
		{
			mmpParser: mmpParser, proofMode: ProofMode.normal,
			maxNumberOfHypothesisDispositionsForStepDerivation: 0,
			renumber: false,
			removeUnusedStatements: false
		});
	mmpUnifier.unify();
	const textEditArray: TextEdit[] = mmpUnifier.textEditArray;
	expect(textEditArray.length).toBe(1);
	const textEdit: TextEdit = textEditArray[0];
	const expectedText = `
* comment that
  should be left on two lines, with   wierd     spacing preserved

6::                |- ps
* second comment    to be left    unchanged
qed:5:ax-mp        |- ch
`;
	expect(textEdit.newText).toEqual(expectedText);
});

test('expect2 x to unify with &S1', () => {
	const mmpSource = `
* test comment

d2:: |- x = &C2
d1:d2:eqeq1i |- ( &S1 = &C3 <-> &C2 = &C3 )
qed: |- ch`;
	const mmpParserParams: IMmpParserParams = {
		textToParse: mmpSource,
		mmParser: eqeq1iMmParser,
		workingVars: new WorkingVars(kindToPrefixMap)
	};
	const mmpParser: MmpParser = new MmpParser(mmpParserParams);
	// const mmpParser: MmpParser = new MmpParser(mmpSource, eqeq1iMmParser, new WorkingVars(kindToPrefixMap));
	mmpParser.parse();
	const mmpUnifier: MmpUnifier = new MmpUnifier(
		{
			mmpParser: mmpParser, proofMode: ProofMode.normal,
			maxNumberOfHypothesisDispositionsForStepDerivation: 0,
			renumber: false,
			removeUnusedStatements: false
		});
	// const mmpUnifier: MmpUnifier = new MmpUnifier(eqeq1iMmParser.labelToStatementMap, eqeq1iMmParser.outermostBlock,
	// 	eqeq1iMmParser.grammar, new WorkingVars(kindToPrefixMap), ProofMode.normal);
	mmpUnifier.unify();
	const textEditArray: TextEdit[] = mmpUnifier.textEditArray;
	const textEdit: TextEdit = textEditArray[0];
	const expectedText = `
* test comment

d2::                |- x = &C2
d1:d2:eqeq1i       |- ( x = &C3 <-> &C2 = &C3 )
qed::              |- ch
`;
	expect(textEdit.newText).toEqual(expectedText);

});

test('expect &W1 and &W2 to be unified properly', () => {
	const mmpSource = `
* test comment

d1:: |- ( ch -> &W2 )
d2:: |- ( ( &W1 -> ps ) -> ph )
qed:d1,d2:ax-mp |- ph
`;
	const mmpParserParams: IMmpParserParams = {
		textToParse: mmpSource,
		mmParser: eqeq1iMmParser,
		workingVars: new WorkingVars(kindToPrefixMap)
	};
	const mmpParser: MmpParser = new MmpParser(mmpParserParams);
	// const mmpParser: MmpParser = new MmpParser(mmpSource, eqeq1iMmParser, new WorkingVars(kindToPrefixMap));
	mmpParser.parse();
	const mmpUnifier: MmpUnifier = new MmpUnifier(
		{
			mmpParser: mmpParser, proofMode: ProofMode.normal,
			maxNumberOfHypothesisDispositionsForStepDerivation: 0,
			renumber: false,
			removeUnusedStatements: false
		});
	mmpUnifier.unify();
	const textEditArray: TextEdit[] = mmpUnifier.textEditArray;
	const textEdit: TextEdit = textEditArray[0];
	const expectedText = `
* test comment

d1::                |- ( ch -> ps )
d2::                |- ( ( ch -> ps ) -> ph )
qed:d1,d2:ax-mp    |- ph
`;
	expect(textEdit.newText).toEqual(expectedText);
});

test('expect ax6ev to be unified without loop', () => {
	const mmpSource = `
* test comment

d2::ax6ev |- E. &S1 &W1
qed: |- ch
`;
	const mmpParserParams: IMmpParserParams = {
		textToParse: mmpSource,
		mmParser: vexTheoryMmParser,
		workingVars: new WorkingVars(kindToPrefixMap)
	};
	const mmpParser: MmpParser = new MmpParser(mmpParserParams);
	// const mmpParser: MmpParser = new MmpParser(mmpSource, vexTheoryMmParser, new WorkingVars(kindToPrefixMap));
	mmpParser.parse();
	const mmpUnifier: MmpUnifier = new MmpUnifier(
		{
			mmpParser: mmpParser, proofMode: ProofMode.normal,
			maxNumberOfHypothesisDispositionsForStepDerivation: 0,
			renumber: false,
			removeUnusedStatements: false
		});
	mmpUnifier.unify();
	const textEditArray: TextEdit[] = mmpUnifier.textEditArray;
	const textEdit: TextEdit = textEditArray[0];
	const expectedText = `
* test comment

d2::ax6ev          |- E. &S1 &S1 = &S2
qed::              |- ch
`;
	expect(textEdit.newText).toEqual(expectedText);
});

test('expect ax9v1 to be unified in a single step', () => {
	const mmpSource = `
* test comment

d5::ax9v1 |- ( &W5 -> ( &W4 -> z e. y ) )
qed: |- ch
`;
	const mmpParserParams: IMmpParserParams = {
		textToParse: mmpSource,
		mmParser: vexTheoryMmParser,
		workingVars: new WorkingVars(kindToPrefixMap)
	};
	const mmpParser: MmpParser = new MmpParser(mmpParserParams);
	// const mmpParser: MmpParser = new MmpParser(mmpSource, vexTheoryMmParser, new WorkingVars(kindToPrefixMap));
	mmpParser.parse();
	const mmpUnifier: MmpUnifier = new MmpUnifier(
		{
			mmpParser: mmpParser, proofMode: ProofMode.normal,
			maxNumberOfHypothesisDispositionsForStepDerivation: 0,
			renumber: false,
			removeUnusedStatements: false
		});
	mmpUnifier.unify();
	const textEditArray: TextEdit[] = mmpUnifier.textEditArray;
	const textEdit: TextEdit = textEditArray[0];
	const expectedText = `
* test comment

d5::ax9v1          |- ( &S1 = y -> ( z e. &S1 -> z e. y ) )
qed::              |- ch
`;
	expect(textEdit.newText).toEqual(expectedText);
});

test('expect wrong ref not to throw an exception', () => {
	const mmpSource = `
* test comment

d2::                |- &W1
d3::               |- ( &W1 -> ch )
d1:d2,d3a:ax-mp    |- ch
`;
	const mmpParserParams: IMmpParserParams = {
		textToParse: mmpSource,
		mmParser: vexTheoryMmParser,
		workingVars: new WorkingVars(kindToPrefixMap)
	};
	const mmpParser: MmpParser = new MmpParser(mmpParserParams);
	// const mmpParser: MmpParser = new MmpParser(mmpSource, vexTheoryMmParser, new WorkingVars(kindToPrefixMap));
	mmpParser.parse();
	const mmpUnifier: MmpUnifier = new MmpUnifier(
		{
			mmpParser: mmpParser, proofMode: ProofMode.normal,
			maxNumberOfHypothesisDispositionsForStepDerivation: 0,
			renumber: false,
			removeUnusedStatements: false
		});
	mmpUnifier.unify();
	const textEditArray: TextEdit[] = mmpUnifier.textEditArray;
	const textEdit: TextEdit = textEditArray[0];
	expect(textEdit.newText).toEqual(mmpSource);
});

test('MmpParser.uProof.formulaToProofStepMap 1', () => {
	const mmpSource = `h1:: |- ps
* comment
h2:: |- ( ps -> ph )
3:: |- ph
qed:: |- ch`;
	const mmpParserParams: IMmpParserParams = {
		textToParse: mmpSource,
		mmParser: mp2MmParser,
		workingVars: new WorkingVars(kindToPrefixMap)
	};
	const mmpParser: MmpParser = new MmpParser(mmpParserParams);
	// const mmpParser: MmpParser = new MmpParser(mmpSource, mp2MmParser, new WorkingVars(kindToPrefixMap));
	mmpParser.parse();
	const indexPs: number | undefined = mmpParser.mmpProof!.formulaToProofStepMap.get('|- ps');
	expect(indexPs).toBe(0);
	const indexWi: number | undefined = mmpParser.mmpProof!.formulaToProofStepMap.get('|- ( ps -> ph )');
	expect(indexWi).toBe(2);
});

test("Unify() removes search statements", () => {
	const mmpSource = `
* test comment

h50::mp2.1 |- ph
SearchSymbols: x y   SearchComment:  
qed:51:ax-mp |- ch`;
	const parser: MmParser = new MmParser();
	parser.ParseText(mp2Theory);
	const mmpParserParams: IMmpParserParams = {
		textToParse: mmpSource,
		mmParser: parser,
		workingVars: new WorkingVars(kindToPrefixMap)
	};
	const mmpParser: MmpParser = new MmpParser(mmpParserParams);
	// const mmpParser: MmpParser = new MmpParser(mmpSource, parser, new WorkingVars(kindToPrefixMap));
	mmpParser.parse();
	const mmpUnifier: MmpUnifier = new MmpUnifier(
		{
			mmpParser: mmpParser, proofMode: ProofMode.normal,
			maxNumberOfHypothesisDispositionsForStepDerivation: 0,
			renumber: false,
			removeUnusedStatements: false
		});
	mmpUnifier.unify();
	const textEditArray: TextEdit[] = mmpUnifier.textEditArray;
	expect(textEditArray.length).toBe(1);
	const newTextExpected = `
* test comment

h50::mp2.1         |- ph
qed:51:ax-mp       |- ch
`;
	const textEdit: TextEdit = textEditArray[0];
	expect(textEdit.newText).toEqual(newTextExpected);
});

test("Working vars to be unified in a single step", () => {
	const mmpSource = `
* test comment

1::0ss             |- &C1 C_ A
2::eqss            |- ( A = &C1 <-> ( A C_ &C1 /\\ &C2 C_ A ) )
qed::              |- ch`;
	const mmpParserParams: IMmpParserParams = {
		textToParse: mmpSource,
		mmParser: opelcnMmParser,
		workingVars: new WorkingVars(kindToPrefixMap)
	};
	const mmpParser: MmpParser = new MmpParser(mmpParserParams);
	// const mmpParser: MmpParser = new MmpParser(mmpSource, opelcnMmParser, new WorkingVars(kindToPrefixMap));
	mmpParser.parse();
	const mmpUnifier: MmpUnifier = new MmpUnifier(
		{
			mmpParser: mmpParser, proofMode: ProofMode.normal,
			maxNumberOfHypothesisDispositionsForStepDerivation: 0,
			renumber: false,
			removeUnusedStatements: false
		});
	mmpUnifier.unify();
	const textEditArray: TextEdit[] = mmpUnifier.textEditArray;
	expect(textEditArray.length).toBe(1);
	const newTextExpected = `
* test comment

1::0ss             |- (/) C_ A
2::eqss            |- ( A = (/) <-> ( A C_ (/) /\\ (/) C_ A ) )
qed::              |- ch
`;
	const textEdit: TextEdit = textEditArray[0];
	expect(textEdit.newText).toEqual(newTextExpected);
});

test('Removed unused statements', () => {
	const mmpSource = `
* test comment

1::a |- ps
2::   |- ( ps -> ch )
3::b |- ( ps -> ph )
4::   |- ch
qed:1,3:ax-mp |- ph
`;
	// const parser: MmParser = new MmParser();
	// parser.ParseText(axmpTheory);
	const mmpParserParams: IMmpParserParams = {
		textToParse: mmpSource,
		mmParser: mp2MmParser,
		workingVars: new WorkingVars(kindToPrefixMap)
	};
	const mmpParser: MmpParser = new MmpParser(mmpParserParams);
	// const mmpParser: MmpParser = new MmpParser(mmpSource, mp2MmParser, new WorkingVars(kindToPrefixMap));
	mmpParser.parse();
	const mmpUnifier: MmpUnifier = new MmpUnifier(
		{
			mmpParser: mmpParser, proofMode: ProofMode.normal,
			maxNumberOfHypothesisDispositionsForStepDerivation: 0,
			renumber: false,
			removeUnusedStatements: true
		});
	mmpUnifier.unify();
	const textEditArray: TextEdit[] = mmpUnifier.textEditArray;
	expect(textEditArray.length).toBe(1);
	const newTextExpected = `
* test comment

1::a                |- ps
3::b                |- ( ps -> ph )
qed:1,3:ax-mp      |- ph
`;
	const textEdit: TextEdit = textEditArray[0];
	expect(textEdit.newText).toEqual(newTextExpected);
});

test('expect proof not created because notnor is discouraged', () => {
	const mmpSource = `\
$theorem test

* test

h1::test.1          |- -. -. ch
2::notnotr          |- ( -. -. ch -> ch )
qed:1,2:ax-mp      |- ch`;
	const mmpParserParams: IMmpParserParams = {
		textToParse: mmpSource,
		mmParser: impbiiMmParser,
		workingVars: new WorkingVars(kindToPrefixMap)
	};
	const mmpParser: MmpParser = new MmpParser(mmpParserParams);
	// const mmpParser: MmpParser = new MmpParser(mmpSource, impbiiMmParser, new WorkingVars(kindToPrefixMap));
	mmpParser.parse();
	const mmpUnifier: MmpUnifier = new MmpUnifier(
		{
			mmpParser: mmpParser, proofMode: ProofMode.normal,
			maxNumberOfHypothesisDispositionsForStepDerivation: 0,
			renumber: false,
			removeUnusedStatements: true
		});
	mmpUnifier.unify();
	const textEditArray: TextEdit[] = mmpUnifier.textEditArray;
	expect(textEditArray.length).toBe(1);
	const newTextExpected = `\
$theorem test

* test

h1::test.1          |- -. -. ch
2::notnotr          |- ( -. -. ch -> ch )
qed:1,2:ax-mp      |- ch
`;
	const textEdit: TextEdit = textEditArray[0];
	expect(textEdit.newText).toEqual(newTextExpected);
});

test('expect proof to be created because $allowdiscouraged is present (notnor is discouraged)', () => {
	const mmpSource = `\
$theorem test
$allowdiscouraged

* test

h1::test.1          |- -. -. ch
2::notnotr          |- ( -. -. ch -> ch )
qed:1,2:ax-mp      |- ch`;
	const mmpParserParams: IMmpParserParams = {
		textToParse: mmpSource,
		mmParser: impbiiMmParser,
		workingVars: new WorkingVars(kindToPrefixMap)
	};
	const mmpParser: MmpParser = new MmpParser(mmpParserParams);
	// const mmpParser: MmpParser = new MmpParser(mmpSource, impbiiMmParser, new WorkingVars(kindToPrefixMap));
	mmpParser.parse();
	const mmpUnifier: MmpUnifier = new MmpUnifier(
		{
			mmpParser: mmpParser, proofMode: ProofMode.normal,
			maxNumberOfHypothesisDispositionsForStepDerivation: 0,
			renumber: false,
			removeUnusedStatements: true
		});
	mmpUnifier.unify();
	const textEditArray: TextEdit[] = mmpUnifier.textEditArray;
	expect(textEditArray.length).toBe(1);
	const newTextExpected = `\
$theorem test
$allowdiscouraged

* test

h1::test.1          |- -. -. ch
2::notnotr          |- ( -. -. ch -> ch )
qed:1,2:ax-mp      |- ch

$=    wch wn wn wch test.1 wch notnotr ax-mp $.

`;
	const textEdit: TextEdit = textEditArray[0];
	expect(textEdit.newText).toEqual(newTextExpected);
});

test('expect Dummy $d comment', () => {
	const mmpSource = `\
$theorem test

* test

1::elequ2            |- ( w = x -> ( z e. w <-> z e. x ) )
2:1:bibi1d          |- ( w = x -> ( ( z e. w <-> z e. y ) <-> ( z e. x <-> z e. y ) ) )
3:2:albidv         |- ( w = x -> ( A. z ( z e. w <-> z e. y ) <-> A. z ( z e. x <-> z e. y ) ) )
qed::              |- ( A. z ( z e. x <-> z e. y ) -> x = y )
$d w z
$d x z
`;
	const mmpParserParams: IMmpParserParams = {
		textToParse: mmpSource,
		mmParser: eqeq1iMmParser,
		workingVars: new WorkingVars(kindToPrefixMap)
	};
	const mmpParser: MmpParser = new MmpParser(mmpParserParams);
	// const mmpParser: MmpParser = new MmpParser(mmpSource, eqeq1iMmParser, new WorkingVars(kindToPrefixMap));
	mmpParser.parse();
	const mmpUnifier: MmpUnifier = new MmpUnifier(
		{
			mmpParser: mmpParser, proofMode: ProofMode.normal,
			maxNumberOfHypothesisDispositionsForStepDerivation: 0,
			renumber: false,
			removeUnusedStatements: false
		});
	mmpUnifier.unify();
	const textEditArray: TextEdit[] = mmpUnifier.textEditArray;
	expect(textEditArray.length).toBe(1);
	const newTextExpected = `\
$theorem test

* test

1::elequ2            |- ( w = x -> ( z e. w <-> z e. x ) )
2:1:bibi1d          |- ( w = x -> ( ( z e. w <-> z e. y ) <-> ( z e. x <-> z e. y ) ) )
3:2:albidv         |- ( w = x -> ( A. z ( z e. w <-> z e. y ) <-> A. z ( z e. x <-> z e. y ) ) )
qed::              |- ( A. z ( z e. x <-> z e. y ) -> x = y )

$d x z

* Dummy $d constraints are listed below
$d w z
`;
	const textEdit: TextEdit = textEditArray[0];
	expect(textEdit.newText).toEqual(newTextExpected);
});

test('remove duplicated constraints Dummy $d comment', () => {
	const mmpSource = `\
$theorem test

* test

1::elequ2            |- ( w = x -> ( z e. w <-> z e. x ) )
2:1:bibi1d          |- ( w = x -> ( ( z e. w <-> z e. y ) <-> ( z e. x <-> z e. y ) ) )
3:2:albidv         |- ( w = x -> ( A. z ( z e. w <-> z e. y ) <-> A. z ( z e. x <-> z e. y ) ) )
qed::              |- ( A. z ( z e. x <-> z e. y ) -> x = y )
$d x z
$d x z
$d w z
* Dummy $d constraints are listed below
$d w z
$d x z
$d w z
`;
	const mmpParserParams: IMmpParserParams = {
		textToParse: mmpSource,
		mmParser: eqeq1iMmParser,
		workingVars: new WorkingVars(kindToPrefixMap)
	};
	const mmpParser: MmpParser = new MmpParser(mmpParserParams);
	// const mmpParser: MmpParser = new MmpParser(mmpSource, eqeq1iMmParser, new WorkingVars(kindToPrefixMap));
	mmpParser.parse();
	const mmpUnifier: MmpUnifier = new MmpUnifier(
		{
			mmpParser: mmpParser, proofMode: ProofMode.normal,
			maxNumberOfHypothesisDispositionsForStepDerivation: 0,
			renumber: false,
			removeUnusedStatements: false
		});
	mmpUnifier.unify();
	const textEditArray: TextEdit[] = mmpUnifier.textEditArray;
	expect(textEditArray.length).toBe(1);
	const newTextExpected = `\
$theorem test

* test

1::elequ2            |- ( w = x -> ( z e. w <-> z e. x ) )
2:1:bibi1d          |- ( w = x -> ( ( z e. w <-> z e. y ) <-> ( z e. x <-> z e. y ) ) )
3:2:albidv         |- ( w = x -> ( A. z ( z e. w <-> z e. y ) <-> A. z ( z e. x <-> z e. y ) ) )
qed::              |- ( A. z ( z e. x <-> z e. y ) -> x = y )

$d x z

* Dummy $d constraints are listed below
$d w z
`;
	const textEdit: TextEdit = textEditArray[0];
	expect(textEdit.newText).toEqual(newTextExpected);
});

test('Expect Dummy $d constraints to be generated because of DisjVarAutomaticGeneration.GenerateDummy', () => {
	const mmpSource = `\
$theorem test

* test

1::elequ2            |- ( w = x -> ( z e. w <-> z e. x ) )
2:1:bibi1d          |- ( w = x -> ( ( z e. w <-> z e. y ) <-> ( z e. x <-> z e. y ) ) )
3:2:albidv         |- ( w = x -> ( A. z ( z e. w <-> z e. y ) <-> A. z ( z e. x <-> z e. y ) ) )
qed::              |- ( A. z ( z e. x <-> z e. y ) -> x = y )
`;
	const mmpParserParams: IMmpParserParams = {
		textToParse: mmpSource,
		mmParser: eqeq1iMmParser,
		workingVars: new WorkingVars(kindToPrefixMap),
		disjVarAutomaticGeneration: DisjVarAutomaticGeneration.GenerateDummy
	};
	const mmpParser: MmpParser = new MmpParser(mmpParserParams);
	// const mmpParser: MmpParser = new MmpParser(mmpSource, eqeq1iMmParser, new WorkingVars(kindToPrefixMap));
	mmpParser.parse();
	const mmpUnifier: MmpUnifier = new MmpUnifier(
		{
			mmpParser: mmpParser, proofMode: ProofMode.normal,
			maxNumberOfHypothesisDispositionsForStepDerivation: 0,
			renumber: false,
			removeUnusedStatements: false
		});
	mmpUnifier.unify();
	const textEditArray: TextEdit[] = mmpUnifier.textEditArray;
	expect(textEditArray.length).toBe(1);
	const newTextExpected = `\
$theorem test

* test

1::elequ2            |- ( w = x -> ( z e. w <-> z e. x ) )
2:1:bibi1d          |- ( w = x -> ( ( z e. w <-> z e. y ) <-> ( z e. x <-> z e. y ) ) )
3:2:albidv         |- ( w = x -> ( A. z ( z e. w <-> z e. y ) <-> A. z ( z e. x <-> z e. y ) ) )
qed::              |- ( A. z ( z e. x <-> z e. y ) -> x = y )

* Dummy $d constraints are listed below
$d w z
`;
	const textEdit: TextEdit = textEditArray[0];
	expect(textEdit.newText).toEqual(newTextExpected);
});

test('Expect all $d constraints to be generated because of DisjVarAutomaticGeneration.GenerateAll', () => {
	const mmpSource = `\
$theorem test

* test

1::elequ2            |- ( w = x -> ( z e. w <-> z e. x ) )
2:1:bibi1d          |- ( w = x -> ( ( z e. w <-> z e. y ) <-> ( z e. x <-> z e. y ) ) )
3:2:albidv         |- ( w = x -> ( A. z ( z e. w <-> z e. y ) <-> A. z ( z e. x <-> z e. y ) ) )
qed::              |- ( A. z ( z e. x <-> z e. y ) -> x = y )
`;
	const mmpParserParams: IMmpParserParams = {
		textToParse: mmpSource,
		mmParser: eqeq1iMmParser,
		workingVars: new WorkingVars(kindToPrefixMap),
		disjVarAutomaticGeneration: DisjVarAutomaticGeneration.GenerateAll
	};
	const mmpParser: MmpParser = new MmpParser(mmpParserParams);
	// const mmpParser: MmpParser = new MmpParser(mmpSource, eqeq1iMmParser, new WorkingVars(kindToPrefixMap));
	mmpParser.parse();
	const mmpUnifier: MmpUnifier = new MmpUnifier(
		{
			mmpParser: mmpParser, proofMode: ProofMode.normal,
			maxNumberOfHypothesisDispositionsForStepDerivation: 0,
			renumber: false,
			removeUnusedStatements: false
		});
	mmpUnifier.unify();
	const textEditArray: TextEdit[] = mmpUnifier.textEditArray;
	expect(textEditArray.length).toBe(1);
	const newTextExpected = `\
$theorem test

* test

1::elequ2            |- ( w = x -> ( z e. w <-> z e. x ) )
2:1:bibi1d          |- ( w = x -> ( ( z e. w <-> z e. y ) <-> ( z e. x <-> z e. y ) ) )
3:2:albidv         |- ( w = x -> ( A. z ( z e. w <-> z e. y ) <-> A. z ( z e. x <-> z e. y ) ) )
qed::              |- ( A. z ( z e. x <-> z e. y ) -> x = y )

$d x z

* Dummy $d constraints are listed below
$d w z
`;
	const textEdit: TextEdit = textEditArray[0];
	expect(textEdit.newText).toEqual(newTextExpected);
});

test('[Issue #23] Replace working variables when proof is complete', () => {
	const mmpSource = `
* test comment

1::ax-1             |- ( ph -> ( &W1 -> ph ) )
2::ax-1             |- ( ph -> ( ( &W1 -> ph ) -> ph ) )
qed:1,2:mpd        |- ( ph -> ph )`;
	// const parser: MmParser = new MmParser();
	// parser.ParseText(axmpTheory);
	const mmpParserParams: IMmpParserParams = {
		textToParse: mmpSource,
		mmParser: opelcnMmParser,
		workingVars: new WorkingVars(kindToPrefixMap)
	};
	const mmpParser: MmpParser = new MmpParser(mmpParserParams);
	// const mmpParser: MmpParser = new MmpParser(mmpSource, mp2MmParser, new WorkingVars(kindToPrefixMap));
	mmpParser.parse();
	const mmpUnifier: MmpUnifier = new MmpUnifier(
		{
			mmpParser: mmpParser,
			proofMode: ProofMode.normal,
			maxNumberOfHypothesisDispositionsForStepDerivation: 0,
			renumber: false,
			removeUnusedStatements: false
		});
	mmpUnifier.unify();
	const textEditArray: TextEdit[] = mmpUnifier.textEditArray;
	expect(textEditArray.length).toBe(1);
	const newTextExpected = `
* test comment

1::ax-1             |- ( ph -> ( ps -> ph ) )
2::ax-1             |- ( ph -> ( ( ps -> ph ) -> ph ) )
qed:1,2:mpd        |- ( ph -> ph )

$=    wph wps wph wi wph wph wps ax-1 wph wps wph wi ax-1 mpd $.

`;
	const textEdit: TextEdit = textEditArray[0];
	expect(textEdit.newText).toEqual(newTextExpected);
});

test('[Issue #23] Replace two working variables when proof is complete', () => {
	const mmpSource = `
* test comment

1::ax-1             |- ( &W2 -> ( &W1 -> &W2 ) )
2::ax-1             |- ( &W2 -> ( ( &W1 -> &W2 ) -> &W2 ) )
qed:1,2:mpd        |- ( &W2 -> &W2 )`;
	// const parser: MmParser = new MmParser();
	// parser.ParseText(axmpTheory);
	const mmpParserParams: IMmpParserParams = {
		textToParse: mmpSource,
		mmParser: opelcnMmParser,
		workingVars: new WorkingVars(kindToPrefixMap)
	};
	const mmpParser: MmpParser = new MmpParser(mmpParserParams);
	// const mmpParser: MmpParser = new MmpParser(mmpSource, mp2MmParser, new WorkingVars(kindToPrefixMap));
	mmpParser.parse();
	const mmpUnifier: MmpUnifier = new MmpUnifier(
		{
			mmpParser: mmpParser,
			proofMode: ProofMode.normal,
			maxNumberOfHypothesisDispositionsForStepDerivation: 0,
			renumber: false,
			removeUnusedStatements: false
		});
	mmpUnifier.unify();
	const textEditArray: TextEdit[] = mmpUnifier.textEditArray;
	expect(textEditArray.length).toBe(1);
	const newTextExpected = `
* test comment

1::ax-1             |- ( ph -> ( ps -> ph ) )
2::ax-1             |- ( ph -> ( ( ps -> ph ) -> ph ) )
qed:1,2:mpd        |- ( ph -> ph )

$=    wph wps wph wi wph wph wps ax-1 wph wps wph wi ax-1 mpd $.

`;
	const textEdit: TextEdit = textEditArray[0];
	expect(textEdit.newText).toEqual(newTextExpected);
});
