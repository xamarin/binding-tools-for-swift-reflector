//
//  xamarinreflect_main.cpp
//  Swift
//
//  Created by Steve Hawley on 1/20/16.
//
//
#include <sstream>
#include "swift/Subsystems.h"



#include "swift/AST/DiagnosticsFrontend.h"
#include "swift/AST/DiagnosticsSema.h"
#include "swift/AST/IRGenOptions.h"
#include "swift/AST/NameLookup.h"
#include "swift/AST/ReferencedNameTracker.h"
#include "swift/AST/TypeRefinementContext.h"

#include "swift/Basic/FileSystem.h"
#include "swift/Basic/SourceManager.h"
#include "swift/Basic/Timer.h"
#include "swift/Frontend/DiagnosticVerifier.h"
#include "swift/Frontend/Frontend.h"
#include "swift/Frontend/PrintingDiagnosticConsumer.h"
#include "swift/Frontend/SerializedDiagnosticConsumer.h"
#include "swift/Immediate/Immediate.h"
#include "swift/Option/Options.h"
#include "swift/PrintAsObjC/PrintAsObjC.h"
#include "swift/Serialization/SerializationOptions.h"
#include "swift/SILOptimizer/PassManager/Passes.h"
#include "swift/AST/ASTVisitor.h"
#include "swift/AST/ForeignErrorConvention.h"
#include "swift/AST/PrettyStackTrace.h"
#include "swift/AST/TypeVisitor.h"
#include "swift/AST/Comment.h"
#include "swift/AST/ASTPrinter.h"
#include "swift/AST/ExistentialLayout.h"

// FIXME: We're just using CompilerInstance::createOutputFile.
// This API should be sunk down to LLVM.
#include "clang/Frontend/CompilerInstance.h"


#include "llvm/ADT/Statistic.h"
#include "llvm/IR/LLVMContext.h"
#include "llvm/IR/Module.h"
#include "llvm/IRReader/IRReader.h"
#include "llvm/Option/Option.h"
#include "llvm/Option/OptTable.h"
#include "llvm/Support/FileSystem.h"
#include "llvm/Support/Path.h"
#include "llvm/Support/raw_ostream.h"
#include "llvm/Support/TargetSelect.h"
#include "llvm/Support/Timer.h"
#include "llvm/Support/YAMLParser.h"
#include "llvm/Support/Path.h"
#include <memory>
#include <unordered_set>
#include <iostream>

using namespace swift;


class ReflectionPrinter : private DeclVisitor<ReflectionPrinter>, private TypeVisitor<ReflectionPrinter, void, Optional<OptionalTypeKind>> {
    friend ASTVisitor;
    friend TypeVisitor;
public:
    ReflectionPrinter(llvm::raw_pwrite_stream &out, ASTContext &ctx, ModuleDecl *m)
    : _m(m), _ctx(ctx), _out(out), _indentLevel(0)
    {
    }
    
    void reflect()
    {
        SmallVector<Decl *, 64> decls;
        _m->getTopLevelDecls(decls);
        indent(); indent();
        indents();
        LangOptions &langOpts = _ctx.LangOpts;
        
        _out << "<module name=\"" << _m->getName() << "\" swiftVersion=\"" << langOpts.EffectiveLanguageVersion <<  "\">\n";
        indent();
        for (auto iter = decls.begin(); iter != decls.end(); iter++)
        {
            ASTVisitor::visit(*iter);
        }
        exdent();
        indents();
        _out << "</module>\n";
    }
    
private:
    SmallVector<const FunctionType *, 4> openFunctionTypes;
    ModuleDecl *_m;
    ASTContext &_ctx;
    llvm::raw_pwrite_stream &_out;
    std::string currentProtocol;
    int _indentLevel;
    
    void indent() { ++_indentLevel; }
    void exdent() { --_indentLevel; }
    void indents() {
        for (int i=0; i < 3 * _indentLevel; i++)
            _out << ' ';
    }
    
    
    void doInnerFoo(std::string name, std::vector<ValueDecl *> &innerFoo)
    {
        indents();
        _out << "<" << name << ">\n";
        indent();
        for (auto i = innerFoo.begin(); i != innerFoo.end(); i++) {
            ASTVisitor::visit(*i);
        }
        exdent();
        indents();
        _out << "</" << name << ">\n";
    }
    
    void printMembers(DeclRange members)
    {
        if (members.empty())
            return;
        
        std::vector<ValueDecl *> innerClasses;
        std::vector<ValueDecl *> innerStructs;
        std::vector<ValueDecl *> innerEnums;
        indents();
        _out << "<members>\n";
        indent();
        for (auto member : members)
        {
            auto VD = dyn_cast<ValueDecl>(member);
            if (!VD)
                continue;
            if (isa<ClassDecl>(VD))
            {
                innerClasses.push_back(VD);
            }
            else if (isa<StructDecl>(VD)) {
                innerStructs.push_back(VD);
            }
            else if (isa<EnumDecl>(VD)) {
                innerEnums.push_back(VD);
            }
            else {
                ASTVisitor::visit(VD);
            }
        }
        exdent();
        indents();
        _out << "</members>\n";
        if (innerClasses.size() > 0)
            doInnerFoo("innerclasses", innerClasses);
        if (innerStructs.size() > 0)
            doInnerFoo("innerstructs", innerStructs);
        if (innerEnums.size() > 0)
            doInnerFoo("innerenums", innerEnums);
    }
    
    std::string inheritanceKind(Type &t)
    {
        if (t->isExistentialType())
        {
            return "protocol";
        }
        if (t->isAnyClassReferenceType())
        {
            return "class";
        }
        return "unknown";
    }
    
    int nonValueInheritanceCount(ArrayRef<TypeLoc> inherited)
    {
        int count = 0;
        for (auto super : inherited) {
            Type t = super.getType();
            if (t->isAnyClassReferenceType() || t->isExistentialType())
                count ++;
        }
        return count;
    }
    
    bool isValueInheritance(Type t)
    {
        return !(t->isAnyClassReferenceType() || t->isExistentialType());
    }
    
    void printInheritance(NominalTypeDecl *ND, ArrayRef<TypeLoc> inherited)
    {
        bool skipValueInheritance = isa<EnumDecl>(*ND);
        if (inherited.size() <= 0 || (skipValueInheritance && nonValueInheritanceCount(inherited) <= 0))
            return;
        indents();
        _out << "<inherits>\n";
        indent();
        for (auto super : inherited)
        {
            indents();
            PrintOptions opts;
            opts.FullyQualifiedTypes = true;
            Type superType = super.getType();
            if (skipValueInheritance && isValueInheritance(superType))
                continue;
            _out << "<inherit type=\"";
            print(superType, OTK_None);
            _out << "\" inheritanceKind=\"" << inheritanceKind(superType) << "\"/>\n";
        }
        
        exdent();
        indents();
        _out << "</inherits>\n";
        
    }
    
    
    // Ignore other declarations.
    void visitDecl(Decl *D) {
        return;
    }
    
    void handleNominal(NominalTypeDecl *ND, std::string label)
    {
        indents();
        EnumDecl *ED = isa<EnumDecl>(*ND) ? (EnumDecl *)ND : 0;
        ProtocolDecl *PD = isa<ProtocolDecl>(*ND) ? (ProtocolDecl *)ND : 0;
        
        _out << "<typedeclaration kind=\"" << label << "\" name=\"" << ND->getName() << "\"";
        bool isOpen = false;
        _out << " accessibility=\"" << ToString(ND->getFormalAccess()) << "\"";
        isOpen = ND->getFormalAccess() == AccessLevel::Open;
        
        
        _out << " isObjC=\"" << (ND->isObjC() ? "true\"" : "false\"");
        
        bool isDeprecated = ND->getAttrs().getDeprecated(ND->getASTContext()) != nullptr;
        std::string flagAsDeprecated = isDeprecated ?
        " isDeprecated=\"true\"" : " isDeprecated=\"false\"";
        _out << flagAsDeprecated;
        
        bool isUnavailable = ND->getAttrs().getUnavailable(ND->getASTContext()) != nullptr;
        std::string flagAsUnavailable = isUnavailable ?
        " isUnavailable=\"true\"" : " isUnavailable=\"false\"";
        _out << flagAsUnavailable;
        
        
        _out << " isFinal=\"" << ((ND->isFinal() || !isOpen) ? "true\"" : "false\"");
        
        if (ED && ED->getRawType()) {
            _out << " rawType=\"";
            print(ED->getRawType(), OTK_None);
            _out << "\"";
        }
        _out << ">\n";
        indent();
        printInheritance(ND, ND->getInherited());
        if (ND->isGenericContext()) {
            printGenerics(ND->getGenericSignature(), ND->getSelfProtocolDecl() != NULL);
        }
        printMembers(ND->getMembers());
        
        if (ED) {
            indents();
            _out << "<elements>\n";
            indent();
            for (auto Elt : ED->getAllElements()) {
                indents();
                _out << "<element name=\"" << Elt->getName() << "\"";
                auto argTy = Elt->getArgumentInterfaceType();
                if (argTy) {
                    _out << " type=\"";
                    print(argTy, OTK_None);
                    _out << "\"";
                }
                LiteralExpr *lit = Elt->getRawValueExpr();
                lit = nullptr;
                if (auto ILE = cast_or_null<IntegerLiteralExpr>(Elt->getRawValueExpr())) {
                    _out << " intValue =\"";
                    if (ILE->isNegative())
                        _out << "-";
                    _out << ILE->getDigitsText() << "\"";
                }
                _out << " />\n";
            }
            exdent();
            indents();
            _out << "</elements>\n";
        }
        if (PD)
            printAssociatedTypes (PD);
        exdent();
        indents();
        _out << "</typedeclaration>\n";
    }
    
    void printAssociatedTypes (ProtocolDecl *PD)
    {
        auto assocTypes = PD->getAssociatedTypeMembers ();
        if (assocTypes.size() == 0)
            return;
        indents();
        _out << "<associatedtypes>\n";
        indent();
        for (auto assocType : assocTypes) {
            auto name = assocType->getName ();
            auto defaultDefn = assocType->getDefaultDefinitionType ();
            auto conformingProtos = assocType->getConformingProtocols ();
            auto superClass = assocType->getSuperclass ();
            
            indents();
            _out << "<associatedtype name=\"";
            filterString (name.str());
            
            if (defaultDefn) {
                _out << "\" defaulttype=\"";
                print(defaultDefn, OTK_None);
            }
            _out << "\">\n";
            if (superClass || conformingProtos.size() > 0) {
                indent();
                if (superClass) {
                    indents();
                    _out << "<superclass name=\"";
                    print(superClass, OTK_None);
                    _out << "/>\n";
                }
                if (conformingProtos.size() > 0) {
                    indents();
                    _out << "<conformingprotocols>\n";
                    indent();
                    for (auto conformingProto : conformingProtos) {
                        indents();
                        _out << "<conformingprotocol name=\"";
                        filterString(conformingProto->getName().str());
                        _out << "\"/>\n";
                    }
                    exdent();
                    indents();
                    _out << "</conformingprotocols>\n";
                }
                exdent();
            }
            indents();
            _out << "</associatedtype>\n";
        }
        
        exdent();
        indents();
        _out << "</associatedtypes>";
    }
    
    // this is handy for debugging
    std::string TypeKindToString (TypeKind tk)
    {
        switch (tk) {
            case TypeKind::BuiltinInteger: return "BuiltinInteger";
            case TypeKind::BuiltinIntegerLiteral: return "BuiltinIntegerLiteral";
            case TypeKind::BuiltinFloat: return "BuiltinFloat";
            case TypeKind::BuiltinRawPointer: return "BuiltinRawPointer";
            case TypeKind::BuiltinNativeObject: return "BuiltinNativeObject";
            case TypeKind::BuiltinBridgeObject: return "BuiltinBridgeObject";
            case TypeKind::BuiltinUnknownObject: return "BuiltinUnknownObject";
            case TypeKind::BuiltinUnsafeValueBuffer: return "BuiltinUnsafeValueBuffer";
            case TypeKind::BuiltinVector: return "BuiltinVector";
            case TypeKind::Tuple: return "Tuple";
            case TypeKind::Enum: return "Enum";
            case TypeKind::Struct: return "Struct";
            case TypeKind::Class: return "Class";
            case TypeKind::Protocol: return "Protocol";
            case TypeKind::BoundGenericClass: return "BoundGenericClass";
            case TypeKind::BoundGenericEnum: return "BoundGenericEnum";
            case TypeKind::BoundGenericStruct: return "BoundGenericStruct";
            case TypeKind::UnboundGeneric: return "UnboundGeneric";
            case TypeKind::Metatype: return "Metatype";
            case TypeKind::ExistentialMetatype: return "ExistentialMetatype";
            case TypeKind::Module: return "Module";
            case TypeKind::DynamicSelf: return "DynamicSelf";
            case TypeKind::Archetype: return "Archetype";
            case TypeKind::GenericTypeParam: return "GenericTypeParam";
            case TypeKind::DependentMember: return "DependentMember";
            case TypeKind::Function: return "Function";
            case TypeKind::GenericFunction: return "GenericFunction";
            case TypeKind::SILFunction: return "SILFunction";
            case TypeKind::SILBlockStorage: return "SILBlockStorage";
            case TypeKind::SILBox: return "SILBox";
            case TypeKind::SILToken: return "SILToken";
            case TypeKind::ProtocolComposition: return "ProtocolComposition";
            case TypeKind::LValue: return "LValue";
            case TypeKind::InOut: return "InOut";
            case TypeKind::TypeVariable: return "TypeVariable";
            case TypeKind::Paren: return "Paren";
            case TypeKind::ArraySlice: return "ArraySlice";
            case TypeKind::Optional: return "Optional";
            case TypeKind::Dictionary: return "Dictionary";
            default: return "unknown";
        }
    }
    
    void visitClassDecl(ClassDecl *CD) {
        handleNominal(CD, "class");
    }
    
    void visitStructDecl(StructDecl *SD) {
        handleNominal(SD, "struct");
    }
    
    void visitEnumDecl(EnumDecl *ED) {
        handleNominal(ED, "enum");
    }
    
    void visitProtocolDecl(ProtocolDecl *PD) {
        // protocols can't nest, this is safe
        currentProtocol = PD->getName().str();
        handleNominal(PD, "protocol");
    }
    
    void visitExtensionDecl(ExtensionDecl *ED) {
        indents();
        _out << "<extension onType =\"";
        print(ED->getExtendedType(), OTK_None);
        _out << "\">\n";
        indent();
        auto protocols = ED->getLocalProtocols(ConformanceLookupKind::OnlyExplicit);
        if (protocols.begin() != protocols.end()) {
            indents();
            _out << "<inherits>\n";
            indent();
            for (auto proto : protocols)
            {
                indents();
                PrintOptions opts;
                opts.FullyQualifiedTypes = true;
                _out << "<inherit type=\"";
                auto module = proto->getModuleContext();
                _out << module->getFullName() << '.' << proto->getFullName();
                _out << "\" inheritanceKind=\"protocol\"/>\n";
            }
            
            exdent();
            indents();
            _out << "</inherits>\n";
        }
        
        printMembers(ED->getMembers());
        exdent();
        indents();
        _out << "</extension>\n";
        
    }
    
    std::string GetObjcSelector (ArrayRef<Identifier> selectorPieces, int argCount)
    {
        std::string result;
        for (unsigned i = 0, n = selectorPieces.size(); i != n; ++i) {
            result.append(selectorPieces[i].str());
            if (i > 0 || argCount > 0)
                result.append(":");
        }
        return result;
    }
    
    std::string ToString(StorageImplInfo &storage)
    {
        if (storage.supportsMutation()) {
            auto writeKind = storage.getWriteImpl();
            switch (writeKind) {
                case WriteImplKind::Immutable: return "Immutable"; // shouldn't happen
                case WriteImplKind::Stored: return "Stored";
                case WriteImplKind::StoredWithObservers: return "StoredWithObservers";
                case WriteImplKind::InheritedWithObservers: return "InheritedWithObservers";
                case WriteImplKind::Set: return "Computed";
                case WriteImplKind::MutableAddress: return "MutableAddressor";
                case WriteImplKind::Modify: return "Coroutine";
            }
        } else {
            auto readKind = storage.getReadImpl();
            switch (readKind) {
                case ReadImplKind::Stored: return "Stored";
                case ReadImplKind::Inherited: return "Inherited";
                case ReadImplKind::Get: return "Computed";
                case ReadImplKind::Address: return "Addressed";
                case ReadImplKind::Read: return "Coroutine";
            }
        }
    }
    
    std::string ToString(AccessLevel access)
    {
        switch (access) {
            case AccessLevel::Internal: return "Internal";
            case AccessLevel::Public: return "Public";
            case AccessLevel::Private: return "Private";
            case AccessLevel::FilePrivate: return "Private"; // FIXME
            case AccessLevel::Open: return "Open";
        }
    }
    
    void visitVarDecl(VarDecl *VD)
    {
        indents();
        
        auto storageInfo = VD->getImplInfo();
        AccessLevel effaccess = VD->getFormalAccess();
        bool isDeprecated = VD->getAttrs().getDeprecated(VD->getASTContext());
        bool isUnavailable = VD->getAttrs().getUnavailable(VD->getASTContext()) != nullptr;
        bool isOptional = VD->getAttrs().getAttribute<OptionalAttr>() != 0;

        
        _out << "<property name=\"" << VD->getName() << "\" type=\"";
        
        print(VD->getInterfaceType(), OTK_None);
        
        _out << "\" storage=\"" << ToString(storageInfo) << "\""
        
        << " accessibility=\"" << ToString(effaccess) << "\""
        
        << " isDeprecated=\"" << (isDeprecated ? "true\"" : "false\"")
        
        << " isUnavailable=\"" << (isUnavailable ? "true\"" : "false\"")
        
        << " isStatic=\"" << (VD->isStatic() ? "true\"" : "false\"")
        
        << " isLet=\"" << (VD->isLet() ? "true\"" : "false\"")
        
        << " isOptional=\"" << (isOptional ? "true\"" : "false\"")
        
        << " />\n";

    bool isComputed = storageInfo.getReadImpl() == ReadImplKind::Get;
	if (!VD->getDeclContext()->isTypeContext() && isComputed && VD->getGetter() != nullptr) {
                printAbstractFunction(VD->getGetter(), false, false);
                if (VD->getSetter() != nullptr)
                        printAbstractFunction(VD->getSetter(), false, false);
        }
    }
    
    
    void visitNameAliasType(NameAliasType *aliasTy,
                            Optional<OptionalTypeKind> optionalKind) {
        const TypeAliasDecl *alias = aliasTy->getDecl();
        _out << alias->getNameStr();
        if (alias->getUnderlyingTypeLoc().getType())
            visitPart(alias->getUnderlyingTypeLoc().getType(), optionalKind);
    }
    
    void filterString(std::string str)
    {
        for (auto c : str)
        {
            if (c == '<')
                _out << "&lt;";
            else if (c == '>')
                _out << "&gt;";
            else if (c == '"')
                _out << "&quot;";
            else if (c == '\'')
                _out << "&apos;";
            else if (c == '&')
                _out << "&amp;";
            else
                _out << c;
        }
    }
    
    void visitBoundGenericType (BoundGenericType *Ty, Optional<OptionalTypeKind> optionalKind)
    {
        if (auto ParentType = Ty->getParent()) {
            visitPart(ParentType, OTK_None);
            _out << ".";
        } else {
            ModuleDecl *Mod = Ty->getDecl()->getModuleContext();
            _out << Mod->getNameStr() << ".";
        }
        TypeDecl *TD = Ty->getDecl();
        _out << TD->getNameStr();
        _out << "&lt;";
        
        ArrayRef<Type> args = Ty->getGenericArgs();
        if (!args.empty()) {
            for (unsigned i = 0, end = args.size(); i != end; i++) {
                if (i)
                    _out << ", ";
                visitType (args[i]->getDesugaredType(), OTK_None);
            }
        }
        
        _out << "&gt;";
    }
    
    void visitType(TypeBase *Ty, Optional<OptionalTypeKind> optionalKind) {
        assert(Ty->getDesugaredType() == Ty && "unhandled sugared type");
        if (auto bgt = dyn_cast<BoundGenericType>(Ty)) {
            visitBoundGenericType (bgt, OTK_None);
        } else if (Ty->getKind() == TypeKind::Protocol) {
            auto canon = Ty->getCanonicalType();
            ProtocolType *PT = dyn_cast<ProtocolType>(canon);
            auto proto = PT->getDecl();
            auto module = proto->getModuleContext();
            _out << module->getFullName() << '.' << proto->getFullName();
        } else {
            PrintOptions opts;
            opts.FullyQualifiedTypes = true;
            opts.PrintNameAliasUnderlyingType = true;
            std::string result = Ty->getString(opts);
            filterString(result);
        }
    }
    
    void visitConstructorDecl(ConstructorDecl *CD) {
        // all constructors get shadowed in a class declaration whether or not they're
        // in the class formally. A stub implementation is there to fail at runtime if called.
        if (CD->hasStubImplementation ())
            return;
        printAbstractFunction(CD, false, CD->isRequired());
    }
    
    void visitDestructorDecl(DestructorDecl *DD)
    {
        printAbstractFunction(DD, false, false);
    }
    
    void visitFuncDecl(FuncDecl *FD) {
        printAbstractFunction(FD, FD->isStatic(), false);
    }
    
    void visitPart(Type ty, Optional<OptionalTypeKind> optionalKind) {
        TypeVisitor::visit(ty, optionalKind);
    }
    
    void visitSyntaxSugarType(SyntaxSugarType *SST,
                              Optional<OptionalTypeKind> optionalKind) {
        visitPart(SST->getSinglyDesugaredType(), optionalKind);
    }
    
    void visitDictionaryType(DictionaryType *DT,
                             Optional<OptionalTypeKind> optionalKind) {
        visitPart(DT->getSinglyDesugaredType(), optionalKind);
    }
    
    void visitArraySliceType(ArraySliceType *AT,
                             Optional<OptionalTypeKind> optionalKind) {
        visitPart(AT->getSinglyDesugaredType(), optionalKind);
    }
    
    void visitProtocolCompositionType(ProtocolCompositionType *PCT,
                                      Optional<OptionalTypeKind> optionalKind) {
        ExistentialLayout layout = PCT->getExistentialLayout ();
        printExistentialLayout (layout, optionalKind);
    }

    void printExistentialLayout (ExistentialLayout layout, Optional<OptionalTypeKind> optionalKind)
    {
        if (layout.isAnyObject ()) {
            _out << "Swift.AnyObject";
            return;
        }
        int i = 0;
        for (auto memType : layout.getProtocols()) {
            if (i > 0)
                _out << " &amp; ";
            print (memType, optionalKind);
            i++;
        }
    }
    
    void print(Type ty, Optional<OptionalTypeKind> optionalKind)
    {
        decltype(openFunctionTypes) savedFunctionTypes;
        savedFunctionTypes.swap(openFunctionTypes);
        
        if (ty->getKind() == TypeKind::Protocol) {
            auto canon = ty->getCanonicalType();
            ProtocolType *PT = dyn_cast<ProtocolType>(canon);
            auto proto = PT->getDecl();
            auto module = proto->getModuleContext();
            _out << module->getFullName() << '.' << proto->getFullName();
        }
        else if (ty->getKind() == TypeKind::ProtocolComposition) {
            if (ty->isAny()) {
                _out << "Swift.Any";
            } else {
                // ProtocolComposition types (p: A & B) have the same issue as protocols. For whatever reason,
                // the swift code doesn't print the fully qualified name.
                ExistentialLayout layout = ty->getExistentialLayout();
                printExistentialLayout (layout, optionalKind);
            }
        } else {
            visitPart(ty->getDesugaredType(), optionalKind);
        }
        
        while (!openFunctionTypes.empty()) {
            const FunctionType *openFunctionTy = openFunctionTypes.pop_back_val();
            openFunctionTy = nullptr;
        }
        
        openFunctionTypes = std::move(savedFunctionTypes);
    }
    
    template <typename T>
    static const T *findClangBase(const T *member) {
        while (member) {
            if (member->getClangDecl())
                return member;
            member = member->getOverriddenDecl();
        }
        return nullptr;
    }
    
    void printSingleMethodParam(const ParamDecl *param, bool isLastPiece, ProtocolDecl * parentProtocol, ParameterTypeFlags paramFlags)
    {
        _out << " type=\"";
        // so yeah, apparently if you have a method within a protocol, you'll see the type set to "Self"
        // instead of the protocol type.
        
        
        if (parentProtocol && (param->getInterfaceType()->getString() == "Self" || param->getInterfaceType()->getString() == "inout Self")) {
            _out << _m->getName().str() << "." << currentProtocol;
        }
        else {
            if (paramFlags.isInOut()) {
                _out << "inout ";
                print (param->getInterfaceType()->getInOutObjectType(), OTK_None);
            }
            else {
                bool isEscaping = paramFlags.isEscaping();
                // why square brackets, you might ask?
                // It turns out that the language of attributes in swift is ambiguous.
                // You can have
                // @token | @token(balanced-tokens) | @token[balanced-tokens]  @token{balanced-tokens}
                // the problem is that when you have this:
                // func foo(a: @escaping ()->()) ...
                // does the parens after @escaping apply to @escaping or the type afterwards?
                // You need more look-ahead than I want to put into the parsing code, which is LL(1)
                // replace it with square brackets and the ambiguity goes away
                
                bool isAutoClosure = paramFlags.isAutoClosure();
                if (isAutoClosure)
                    _out << "@autoclosure[] ";
                if (isEscaping)
                    _out << "@escaping[] ";
                
                
                print(param->getInterfaceType(), OTK_None);
            }
        }
        _out << "\"";
        Identifier publicName = param->getArgumentName();
	std::string publicNameStr = publicName.empty() ? "" : publicName.str();
	std::string privateNameStr = param->getName().str();

	_out << " publicName=\"";
	filterString (publicNameStr);
	_out << "\" privateName=\"";
	filterString (privateNameStr);
        _out << "\" isVariadic=\"" << (param->isVariadic () ? "true" : "false");
	_out << "\"";
    }
    
    void printParameterList(AbstractFunctionDecl *AFD, ArrayRef<ParamDecl*> params)
    {
        ProtocolDecl * parentProtocol = AFD->getParent()->getSelfProtocolDecl();
        
        for (unsigned i = 0; i < params.size(); i++) {
            indents();
            _out << "<parameter index=\"" << i << "\"";
            auto p = params[i];
            auto flags = ParameterTypeFlags::fromParameterType(p->getInterfaceType(), p->isVariadic(), p->isAutoClosure(), p->getValueOwnership());
            printSingleMethodParam(p, i == params.size() - 1, parentProtocol, flags);
            _out << "/>\n";
        }
    }
    
    void printParameterLists(AbstractFunctionDecl *AFD)
    {
        
        Type curTy = nullptr;
        if (AFD->getDeclContext()->isTypeContext()) {
            curTy = AFD->getDeclContext()->getDeclaredInterfaceType();
        }
        auto parentProtocol = AFD->getParent()->getSelfProtocolDecl();
        
        indents();
        _out << "<parameterlists>\n";
        indent();
        int index = 0;
        if (curTy) {
            indents();
            _out << "<parameterlist index=\"0\">\n";
            indent();
            indents();
            _out << "<parameter type=\"";
            if (parentProtocol && (curTy->getString() == "Self" || curTy->getString() == "inout Self")) {
                _out << _m->getName().str() << "." << currentProtocol;
            }
            else {
                if (!curTy->getClassOrBoundGenericClass()) {
                    _out << "inout ";
                }
                print (curTy, OTK_None);
                if (isa<ConstructorDecl>(AFD) || isa<DestructorDecl>(AFD))
                {
                    _out << ".Type";
                }
            }
            _out << "\" index=\"0\" publicName=\"\" privateName=\"self\" isVariadic=\"false\" />";
            indents();
            _out << "</parameterlist>\n";
            index++;
        }

        
        
        const auto &params = AFD->getParameters()->getArray();
        indents();
        _out << "<parameterlist index=\"" << index << "\">\n";
            indent();
        printParameterList(AFD, params);
        exdent();
        indents();
        _out << "</parameterlist>\n";

        exdent();
        indents();
        _out << "</parameterlists>\n";
    }
    
    void printGenerics(GenericSignature *generics, bool isProtocol)
    {
        bool hasSome = false;
        for (auto gen : generics->getGenericParams()) {
            if (gen->getName().str() == "Self" && isProtocol)
                continue;
            if (!hasSome) {
                indents();
                _out << "<genericparameters>\n";
                indent();
                hasSome = true;
            }
            indents();
            _out << "<param name=\"" << gen->getName().str() << "\"/>\n";
        }
        if (hasSome) {
            for (auto req : generics->getRequirements()) {
                indents();
                if (req.getKind() == RequirementKind::Conformance ||
                    req.getKind() == RequirementKind::Superclass) {
                    _out << "<where name=\"" << req.getFirstType().getString() << "\" relationship=\"inherits\" from=\"";
                    print(req.getSecondType(), OTK_None);
                    _out << "\" />\n";
                }
                else if (req.getKind() == RequirementKind::SameType) {
                    _out << "<where firsttype=\"";
                    print(req.getFirstType(), OTK_None);
                    _out << "\" relationship=\"equals\" secondtype=\"";
                    print(req.getSecondType(), OTK_None);
                    _out << "\" />\n";
                }
                else {
                    // uh...
                }
            }
            exdent();
            indents();
            _out << "</genericparameters>\n";
        }
    }
    
    void xxprintGenericParameters(GenericParamList *generics, bool isProtocol)
    {
        bool hasSome = false;
        for (auto gen : generics->getParams()) {
            if (gen->getNameStr() == "Self" && isProtocol)
                continue;
            if (!hasSome) {
                indents();
                _out << "<genericparameters>\n";
                indent();
                hasSome = true;
            }
            indents();
            _out << "<param name=\"" << gen->getNameStr() << "\"/>\n";
        }
        if (hasSome) {
            for (auto req : generics->getRequirements()) {
                indents();
                if (req.getKind() == RequirementReprKind::TypeConstraint) {
                    _out << "<where name=\"" << req.getSubject().getString() << "\" relationship=\"inherits\" from=\"";
                    print(req.getConstraint(), OTK_None);
                    _out << "\" />\n";
                }
                else {
                    _out << "<where firsttype=\"";
                    print(req.getFirstType(), OTK_None);
                    _out << "\" relationship=\"equals\" secondtype=\"";
                    print(req.getSecondType(), OTK_None);
                    _out << "\" />\n";
                    
                }
            }
            exdent();
            indents();
            _out << "</genericparameters>\n";
        }
    }
    
    StringRef getPropertyName (ObjCSelector sel)
    {
        auto selStr = sel.getSelectorPieces()[0].str();
        // Getting property names is apparently hard in swift 5. The most reliable way seems to be to
        // get the ObjC selector for that property and the first element is reliably the property name.
        // why check the args? in case someone decides to name a property in swift
        // objectAtIndexedSubscript
        if ((selStr == "objectAtIndexedSubscript" || selStr == "objectForKeyedSubscript") && sel.getNumArgs() >= 1)
            selStr = "subscript";
        return selStr;
    }

    void printAbstractFunction(AbstractFunctionDecl *AFD, bool isClassMethod, bool isRequired) {
        
        
        // helps debugging
        //        Type theType = AFD->getType();
        //        auto theKind = theType->getKind();
        //        ObjCSelector sel = AFD->getObjCSelector();
        //        DeclName declName = AFD->getFullName();
        
        
        auto ty = AFD->getDeclContext()->isTypeContext() ?
        AFD->getMethodInterfaceType() : AFD->getInterfaceType();
        
        AbstractStorageDecl *AD = nullptr;
        if (isa<AccessorDecl>(AFD)) {
            auto acc = cast<AccessorDecl>(AFD);
            AD = acc->getStorage();
        }
        
        Type resultTy = ty->castTo<AnyFunctionType>()->getResult();
        resultTy = resultTy->getDesugaredType ();
        
        bool isDeprecated = AFD->getAttrs().getDeprecated(AFD->getASTContext());
        std::string flagAsDeprecated = isDeprecated ?
        " isDeprecated=\"true\" " : " isDeprecated=\"false\" ";
        bool isUnavailable = AFD->getAttrs().getUnavailable(AFD->getASTContext()) != nullptr;
        std::string flagAsUnavailable = isUnavailable ?
        " isUnavailable=\"true\"" : " isUnavailable=\"false\"";
        bool isConvenienceInit = false;
        
        
        std::string name;
        std::string flagAsProperty = "isProperty=\"false\" ";
        
        if (isa<ConstructorDecl>(AFD))
        {
            name = ".ctor";
            isConvenienceInit = ((ConstructorDecl *)AFD)->isConvenienceInit();
        }
        else if (isa<DestructorDecl>(AFD))
        {
            name = ".dtor";
        }
        else {
            name = AFD->getNameStr();
        }
        if (name == "_") {
            if (isa<AccessorDecl>(AFD) && isa<FuncDecl>(AFD)) {
                AccessorDecl *accessorDecl = (AccessorDecl *)AFD;
                if (auto *ASD = accessorDecl->getStorage())
                {
                    switch(accessorDecl->getAccessorKind())
                    {
                        case AccessorKind::Get: name = "get_"; break;
                        case AccessorKind::Set: name = "set_"; break;
                        case AccessorKind::WillSet: name = "willset_"; break;
                        case AccessorKind::DidSet: name = "didset_"; break;
                        case AccessorKind::Modify: name = "materializeforset_"; break;
                        case AccessorKind::Address: name = "addressor_"; break;
                        case AccessorKind::MutableAddress: name = "mutableaddressor_"; break;
                        case AccessorKind::Read: name = "reader_"; break;
                    }
                    
                    if (accessorDecl->isGetter()) {
                        name += getPropertyName (ASD->getObjCGetterSelector());
                    }
                    else if (accessorDecl->isSetter()) {
                        name += getPropertyName (ASD->getObjCGetterSelector());
                    }
                    flagAsProperty = "isProperty=\"true\" ";
                }
            }
        }
        
        bool isOptional = AFD->getAttrs().hasAttribute<OptionalAttr>();
        if (AD != nullptr) {
            isOptional = AD->getAttrs().hasAttribute<OptionalAttr>();
        }
        
        bool mutating = false;
        if (isa<FuncDecl>(AFD)) {
            FuncDecl *FD = (FuncDecl *)AFD;
            mutating = FD->isMutating();
        }
        
        std::string operatorKind = "\"None\"";
        if (AFD->isOperator()) {
            FuncDecl *FS = (FuncDecl *)AFD;
            OperatorDecl *op = FS->getOperatorDecl();
            switch (op->getKind()) {
                case DeclKind::PrefixOperator:
                    operatorKind = "\"Prefix\"";
                    break;
                case DeclKind::PostfixOperator:
                    operatorKind = "\"Postfix\"";
                    break;
                case DeclKind::InfixOperator:
                    operatorKind = "\"Infix\"";
                    break;
                default:
                    operatorKind = "\"Unknown\"";
                    break;
            }
        }
        
        const auto &params = AFD->getParameters();
        auto argCount = params->size();
        
        indents();
        _out << "<func name=\"";
        filterString(name);
        
        _out << "\" " << flagAsProperty << "returnType=\"";
        
        print(resultTy, OTK_None);
        AccessLevel access = AFD->getFormalAccess();
        _out << "\" accessibility=\"" << ToString(access);
        _out << "\" isStatic=\"" << (AFD->isStatic() ? "true" : "false") <<
        "\" hasThrows=\"" << (AFD->hasThrows() ? "true" : "false") <<
        "\" isFinal=\"" << (AFD->isFinal() ? "true" : "false") <<
        "\" isOptional=\"" << (isOptional ? "true" : "false") <<
        "\" isConvenienceInit=\"" << (isConvenienceInit ? "true" : "false") <<
        "\" objcSelector=\"";
        filterString(GetObjcSelector(AFD->getObjCSelector().getSelectorPieces(), argCount));
        _out << "\" operatorKind=" << operatorKind <<
        flagAsDeprecated << flagAsUnavailable <<
        " isMutating=\"" << (mutating ? "true" : "false") << "\"";
        if (isRequired) {
            _out << " isRequired=\"true\"";
        }
        _out << ">\n";
        indent();
        
        if (AFD->isGeneric()) {
            printGenerics(AFD->getGenericSignature(), false);
        }
        
        printParameterLists(AFD);
        
        
        exdent();
        indents();
        _out << "</func>\n";
    }
    
};


int xamreflect_main(ArrayRef<const char *>Args,
                    const char *Argv0, void *MainAddr) {
    using namespace llvm::sys;
    llvm::InitializeAllTargets();
    llvm::InitializeAllTargetMCs();
    llvm::InitializeAllAsmPrinters();
    llvm::InitializeAllAsmParsers();
    
    CompilerInstance Instance;
    PrintingDiagnosticConsumer PDC;
    Instance.addDiagnosticConsumer(&PDC);
    
    if (Args.empty()) {
        Instance.getDiags().diagnose(SourceLoc(), diag::error_no_frontend_args);
        return 1;
    }
    
    CompilerInvocation Invocation;
    std::string MainExecutablePath = llvm::sys::fs::getMainExecutable(Argv0,
                                                                      MainAddr);
    Invocation.setMainExecutablePath(MainExecutablePath);
    
    SmallString<128> workingDirectory;
    llvm::sys::fs::current_path(workingDirectory);
    
    // Parse arguments.
    SmallVector<std::unique_ptr<llvm::MemoryBuffer>, 4> configurationFileBuffers;
    if (Invocation.parseArgs(Args, Instance.getDiags(), &configurationFileBuffers, workingDirectory)) {
        return 1;
    }

    // swift 5 broke output file handling. Thanks.
    const char *outputPath = nullptr;
    for (size_t i =0; i < Args.size(); i++) {
        if (strcmp("-o", Args[i]) == 0 && i < Args.size() - 1) {
            outputPath = Args[i + 1];
            break;
        }
    }
    
    FrontendOptions opts = Invocation.getFrontendOptions();
    
    clang::CompilerInstance Clang;
    std::string tmpFilePath;
    std::error_code EC;
    std::unique_ptr<llvm::raw_pwrite_stream> out =
    Clang.createOutputFile(outputPath, EC,
                           /*binary=*/false,
                           /*removeOnSignal=*/true,
                           /*inputPath=*/"",
                           path::extension(outputPath),
                           /*temporary=*/false,
                           /*createDirs=*/false,
                           /*finalPath=*/nullptr,
                           nullptr);
    
    if (!out) {
        Instance.getDiags().diagnose(SourceLoc(), diag::error_opening_output,
                                     outputPath, EC.message());
    }
    
    std::vector<std::string> fileNames;
    for (auto fileName : opts.InputsAndOutputs.getInputFilenames())
    {
        fileNames.push_back(fileName);
    }
    // if we leave the InputFilenames in there then Instance.setup() screams because it
    // doesn't like opening modules.
    Invocation.getFrontendOptions().InputsAndOutputs.clearInputs();
    
    
    if (Instance.setup(Invocation)) { // this fails on the module(s), but we have everything else we need
        return 1;
    }
    
    *out << "<?xml version=\"1.0\" encoding=\"utf-8\"?>\n<xamreflect version=\"1.0\">\n   <modulelist>\n";
    
    for (auto fileName = fileNames.begin(); fileName != fileNames.end(); fileName++)
    {
        ASTContext &astctx = Instance.getASTContext();
        Identifier modName = astctx.getIdentifier(*fileName);
        auto *module = astctx.getModule({ std::make_pair(modName, SourceLoc()) });
        if (!module)
        {
            Instance.getDiags().diagnose(SourceLoc(), diag::error_open_input_file,
                                         *fileName, EC.message());
        }
        ReflectionPrinter printer(*out, astctx, module);
        printer.reflect();
    }
    *out << "   </modulelist>\n</xamreflect>\n";
    
    out->flush();
    
    
    return 0;
}


