import { TextEdit } from 'vscode-languageserver';
import { ProofMode } from '../mm/ConfigurationManager';
import { IMmpParserParams, MmpParser } from '../mmp/MmpParser';
import { MmpUnifier } from '../mmp/MmpUnifier';
import { WorkingVars } from '../mmp/WorkingVars';
import { createMmParser, impbiiMmParser, kindToPrefixMap, opelcnMmParser, vexTheoryMmParser } from './GlobalForTest.test';
import { MmParser } from '../mm/MmParser';

test('Expect mmp proof for id theorem, to be inserted', () => {
	// we've decided not to remove the wrong ref
	const mmpSource = `
* comment before

$getproof id
qed:5:impbii |- ch`;
	const mmpParserParams : IMmpParserParams = {
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
* comment before

$theorem id
*    Principle of
     identity.
1::ax-1             |- ( ph -> ( ph -> ph ) )
2::ax-1             |- ( ph -> ( ( ph -> ph ) -> ph ) )
qed:1,2:mpd        |- ( ph -> ph )
qed:5:impbii       |- ch
`;
	expect(textEdit.newText).toEqual(newTextExpected);
});

test('getproof expect eHyps at the top and the duplicated qed with the same formula to be removed', () => {
	const mmpSource = `\
$getproof elabgf
qed: |- ( A e. B -> ( A e. { x | ph } <-> ps ) )`;
	const mmpParserParams : IMmpParserParams = {
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
	const textEdit: TextEdit = textEditArray[0];
	const newTextExpected = `
* MissingComment

$theorem elabgf
h1::elabgf.1          |- F/_ x A
h2::elabgf.2         |- F/ x ps
h3::elabgf.3         |- ( x = A -> ( ph <-> ps ) )
4::nfab1              |- F/_ x { x | ph }
5:1,4:nfel           |- F/ x A e. { x | ph }
6:5,2:nfbi          |- F/ x ( A e. { x | ph } <-> ps )
7::eleq1             |- ( x = A -> ( x e. { x | ph } <-> A e. { x | ph } ) )
8:7,3:bibi12d       |- ( x = A -> ( ( x e. { x | ph } <-> ph ) <-> ( A e. { x | ph } <-> ps ) ) )
9::abid             |- ( x e. { x | ph } <-> ph )
qed:1,6,8,9:vtoclgf
                   |- ( A e. B -> ( A e. { x | ph } <-> ps ) )
qed::              |- ( A e. B -> ( A e. { x | ph } <-> ps ) )
`;
	expect(textEdit.newText).toEqual(newTextExpected);
});

test('getproof expect right order for eHyps at the top', () => {
	const mmpSource = `
* comment before

$getproof mp2`;
	const mmpParserParams : IMmpParserParams = {
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
	const textEdit: TextEdit = textEditArray[0];
	const newTextExpected = `
* comment before

$theorem mp2
h1::mp2.1            |- ph
h2::mp2.2           |- ps
h3::mp2.3            |- ( ph -> ( ps -> ch ) )
4:1,3:ax-mp         |- ( ps -> ch )
qed:2,4:ax-mp      |- ch
`;
	expect(textEdit.newText).toEqual(newTextExpected);
});

test('expect to work for unverified theorem', () => {
	const mmParser: MmParser = createMmParser('impbii-bad.mm');
	const mmpSource = `
* comment before

$getproof simprim`;
	const mmpParserParams : IMmpParserParams = {
		textToParse: mmpSource,
		mmParser: mmParser,
		workingVars: new WorkingVars(kindToPrefixMap)
	};
	const mmpParser: MmpParser = new MmpParser(mmpParserParams);
	// const mmpParser: MmpParser = new MmpParser(mmpSource, mmParser, new WorkingVars(kindToPrefixMap));
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
* comment before

$theorem simprim
1::idd              |- ( ph -> ( ps -> ps ) )
qed:1:impi         |- ( -. ( ph -> -. ps ) -> ps )
`;
	expect(textEdit.newText).toEqual(newTextExpected);
});

test('Expect $d constraints, to be inserted', () => {
	// we've decided not to remove the wrong ref
	const mmpSource = `
* comment before

$getproof dfcleq`;
	const mmpParserParams : IMmpParserParams = {
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
	expect(textEditArray.length).toBe(1);
	const textEdit: TextEdit = textEditArray[0];
	const newTextExpected = `
* comment before

$theorem dfcleq
*      Comment for dfcleq for unit test
1::axext3           |- ( A. x ( x e. y <-> x e. z ) -> y = z )
qed:1:df-cleq      |- ( A = B <-> A. x ( x e. A <-> x e. B ) )

$d A x
$d B x
$d x y
$d x z
$d y z
`;
	expect(textEdit.newText).toEqual(newTextExpected);
});

test('Expect mmp proof for mp2 theorem to be inserted, even though it is written in normal mode', () => {
	// we've decided not to remove the wrong ref
	const mmpSource = `
* comment before

$getproof mp2
qed:5:impbii |- ch`;
	const mmpParserParams : IMmpParserParams = {
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
* comment before

$theorem mp2
*      A double modus ponens inference.
h1::mp2.0            |- ph
h2::mp2.2           |- ps
h3::mp2.3            |- ( ph -> ( ps -> ch ) )
4:1,3:ax-mp         |- ( ps -> ch )
qed:2,4:ax-mp      |- ch
qed:5:impbii       |- ch
`;
	expect(textEdit.newText).toEqual(newTextExpected);
});