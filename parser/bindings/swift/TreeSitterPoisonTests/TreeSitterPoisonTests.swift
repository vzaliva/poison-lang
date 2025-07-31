import XCTest
import SwiftTreeSitter
import TreeSitterPoison

final class TreeSitterPoisonTests: XCTestCase {
    func testCanLoadGrammar() throws {
        let parser = Parser()
        let language = Language(language: tree_sitter_poison())
        XCTAssertNoThrow(try parser.setLanguage(language),
                         "Error loading Poison grammar")
    }
}
