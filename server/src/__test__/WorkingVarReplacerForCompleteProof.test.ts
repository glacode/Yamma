import { Diagnostic, DiagnosticSeverity, TextDocuments } from 'vscode-languageserver';
import { TextDocument } from 'vscode-languageserver-textdocument';
import { GlobalState } from '../general/GlobalState';
import { ConfigurationManager, defaultSettings, DisjVarAutomaticGeneration, LabelsOrderInCompressedProof, ProofMode, DiagnosticMessageForSyntaxError, IExtensionSettings, IVariableKindConfiguration } from '../mm/ConfigurationManager';
import { MmParser } from '../mm/MmParser';
import { IMmpParserParams, MmpParser, MmpParserWarningCode } from '../mmp/MmpParser';
import { OnUnifyHandler, UnifyAndValidateArgs } from '../languageServerHandlers/OnUnifyHandler';
import { WorkingVars } from '../mmp/WorkingVars';
import { kindToPrefixMap, mp2Theory } from './GlobalForTest.test';
import { Connection } from 'vscode-languageserver';

test('WorkingVarReplacerForCompleteProof diagnostics', async () => {
	const mmpSource = `\
$theorem test

* test comment

h1::test.1            |- &W4
h2::test.2            |- ( &W4 -> &W3 )
h3::test.3           |- ( &W3 -> &W1 )
h4::test.4          |- ( &W1 -> &W2 )
5:1,2:ax-mp          |- &W3
6:5,3:ax-mp         |- &W1
qed:6,4:ax-mp      |- &W2`;

	const globalState: GlobalState = new GlobalState();

	// Initialize globalState.lastFetchedSettings for WorkingVars
	const variableKindsConfiguration: Map<string, IVariableKindConfiguration> = new Map<string, IVariableKindConfiguration>();
	variableKindsConfiguration.set('wff', { workingVarPrefix: 'W', lspSemantictokenType: 'variable' });
	variableKindsConfiguration.set('setvar', { workingVarPrefix: 'S', lspSemantictokenType: 'string' });
	variableKindsConfiguration.set('class', { workingVarPrefix: 'C', lspSemantictokenType: 'keyword' });

	const extensionSettings: IExtensionSettings = {
		maxNumberOfProblems: 100,
		mmFileFullPath: '',
		disjVarAutomaticGeneration: DisjVarAutomaticGeneration.GenerateDummy,
		proofMode: ProofMode.normal,
		labelsOrderInCompressedProof: LabelsOrderInCompressedProof.mostReferencedFirstAndNiceFormatting,
		diagnosticMessageForSyntaxError: DiagnosticMessageForSyntaxError.short,
		variableKindsConfiguration: variableKindsConfiguration
	};
	globalState.lastFetchedSettings = extensionSettings;

	const mmParser: MmParser = new MmParser(globalState);
	mmParser.ParseText(mp2Theory);
	mmParser.createParseNodesForAssertionsSync();
	globalState.mmParser = mmParser;

	// Prepare ConfigurationManager
	const mockExtensionConfiguration = {
		mmFileFullPath: '',
		disjVarAutomaticGeneration: DisjVarAutomaticGeneration.GenerateDummy,
		maxNumberOfProblems: 100,
		proofMode: ProofMode.normal,
		labelsOrderInCompressedProof: LabelsOrderInCompressedProof.mostReferencedFirstAndNiceFormatting,
		diagnosticMessageForSyntaxError: DiagnosticMessageForSyntaxError.short,
		kindConfigurations: [
			{ variablekind: 'wff', workingvarprefix: 'W', lspsemantictokentype: 'variable' },
			{ variablekind: 'setvar', workingvarprefix: 'S', lspsemantictokentype: 'string' },
			{ variablekind: 'class', workingvarprefix: 'C', lspsemantictokentype: 'keyword' }
		]
	};

	const mockConnection = {
		workspace: {
			getConfiguration: jest.fn().mockResolvedValue(mockExtensionConfiguration),
			applyEdit: jest.fn().mockResolvedValue({ applied: true })
		},
		sendDiagnostics: jest.fn(),
		sendNotification: jest.fn(),
		onInitialize: jest.fn()
	} as any as Connection;

	const configurationManager = new ConfigurationManager(true, true, defaultSettings, defaultSettings, mockConnection, globalState);
	globalState.configurationManager = configurationManager;

	// Prepare initial MmpParser (needed for GlobalState.lastMmpParser)
	const mmpParserParams: IMmpParserParams = {
		textToParse: mmpSource,
		mmParser: mmParser,
		workingVars: new WorkingVars(kindToPrefixMap)
	};
	const mmpParser: MmpParser = new MmpParser(mmpParserParams);
	mmpParser.parse();
	globalState.lastMmpParser = mmpParser;

	// Prepare Documents
	const uri = 'file:///test.mmp';
	const textDocument = TextDocument.create(uri, 'yamma', 1, mmpSource);
	const mockDocuments = {
		get: (u: string) => u === uri ? textDocument : undefined
	} as any as TextDocuments<TextDocument>;

	const args: UnifyAndValidateArgs = {
		textDocumentUri: uri,
		connection: mockConnection,
		documents: mockDocuments,
		hasConfigurationCapability: true,
		maxNumberOfHypothesisDispositionsForStepDerivation: 0,
		globalState: globalState,
		renumber: false,
		removeUnusedStatements: false
	};

	await OnUnifyHandler.unifyAndValidate(args);

	// Check the resulting edited text
	const applyEditCalls = (mockConnection.workspace.applyEdit as jest.Mock).mock.calls;
	expect(applyEditCalls.length).toBeGreaterThan(0);
	const workspaceEdit = applyEditCalls[0][0];
	const edits = workspaceEdit.changes![uri];
	const resultingText = edits[0].newText;

	const expectedText = `\
$theorem test

* test comment

h1::test.1            |- ph
h2::test.2            |- ( ph -> ps )
h3::test.3           |- ( ps -> ch )
h4::test.4          |- ( ch -> &W2 )
5:1,2:ax-mp          |- ps
6:5,3:ax-mp         |- ch
qed:6,4:ax-mp      |- &W2
`;

	expect(resultingText).toEqual(expectedText);

	// Check if diagnostics were sent
	expect(mockConnection.sendDiagnostics).toHaveBeenCalled();

	// Get the last call arguments
	// The first call might be empty or intermediate, we want to check if any call contained the error
	// But OnDidChangeContentHandler calls sendDiagnostics once per validation.
	// UnifyAndValidate calls requireValidation which triggers validation.
	// unification might trigger it, but here we expect the validation triggered AFTER unification to contain the error.

	const calls = (mockConnection.sendDiagnostics as jest.Mock).mock.calls;
	let foundDiagnostic = false;
	for (const call of calls) {
		const params = call[0]; // PublishDiagnosticsParams
		const diagnostics: Diagnostic[] = params.diagnostics;
		expect(diagnostics.length).toBe(2);
		expect(diagnostics[0].code).toBe(MmpParserWarningCode.proofCompleteButWorkingVarsRemainAndNoUnusedTheoryVars);
		expect(diagnostics[0].message).toBe('No unused variable of kind wff found in the theory');
		expect(diagnostics[0].severity).toBe(DiagnosticSeverity.Warning);
		expect(diagnostics[0].range.start.line).toBe(7);
		expect(diagnostics[0].range.start.character).toBe(32);
		expect(diagnostics[0].range.end.line).toBe(7);
		expect(diagnostics[0].range.end.character).toBe(35);
		expect(diagnostics[1].code).toBe(MmpParserWarningCode.proofCompleteButWorkingVarsRemainAndNoUnusedTheoryVars);
		expect(diagnostics[1].message).toBe('No unused variable of kind wff found in the theory');
		expect(diagnostics[1].severity).toBe(DiagnosticSeverity.Warning);
		expect(diagnostics[1].range.start.line).toBe(10);
		expect(diagnostics[1].range.start.character).toBe(22);
		expect(diagnostics[1].range.end.line).toBe(10);
		expect(diagnostics[1].range.end.character).toBe(25);
		foundDiagnostic = true;
	}

	expect(foundDiagnostic).toBeTruthy();

	// it should be set to false the next unification
	expect(globalState.isProofCompleteAndItContainsWorkingVarsAndThereAreNoUnusedTheoryVars).toBeTruthy();
});