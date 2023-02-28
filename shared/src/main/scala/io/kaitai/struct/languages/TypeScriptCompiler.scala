package io.kaitai.struct.languages

import io.kaitai.struct.datatype.DataType._
import io.kaitai.struct.datatype._
import io.kaitai.struct.exprlang.Ast
import io.kaitai.struct.exprlang.Ast.expr
import io.kaitai.struct.format._
import io.kaitai.struct.languages.components._
import io.kaitai.struct.translators.TypeScriptTranslator
import io.kaitai.struct.{ClassTypeProvider, RuntimeConfig, Utils}

class TypeScriptCompiler(typeProvider: ClassTypeProvider, config: RuntimeConfig)
  extends LanguageCompiler(typeProvider, config)
    with UpperCamelCaseClasses
    with ObjectOrientedLanguage
    with SingleOutputFile
    with AllocateIOLocalVar
    with EveryReadIsExpression
    with UniversalDoc
    with FixedContentsUsingArrayByteLiteral
    with SwitchIfOps
    with NoNeedForFullClassPath {
  import TypeScriptCompiler._

  override val translator = new TypeScriptTranslator(typeProvider)

  override def indent: String = "    "
  override def outFileName(topClassName: String): String = s"${type2class(topClassName)}.ts"

  override def outImports(topClass: ClassSpec): String =
    importList.toList.mkString("", "\n", "\n")
  
  override def normalIO: String = privateMemberName(IoIdentifier)

  override def fileHeader(topClassName: String): Unit = {
    importList.add("import { KaitaiStruct, KaitaiStream } from 'kaitai-struct-ts'")

    outHeader.puts(s"// $headerComment")
    outHeader.puts

    outHeader.puts("interface IDebug {")
    outHeader.inc
    outHeader.puts("start?: number;")
    outHeader.puts("ioOffset?: number;")
    outHeader.puts("end?: number;")
    outHeader.puts("arr?: IDebug[];")
    outHeader.puts("enumName?: string;")
    outHeader.puts("[key: string]: number | string | IDebug | IDebug[] | undefined;")
    outHeader.dec
    outHeader.puts("}")
  }

  override def fileFooter(topClassName: String): Unit = {
    out.puts(s"export default ${type2class(topClassName)};")
  }

  override def opaqueClassDeclaration(classSpec: ClassSpec): Unit = {
    val className = type2class(classSpec.name.head)
    importList.add(s"import $className from './$className.ts'")
  }

  override def classHeader(name: String): Unit = {
    out.puts(s"export class ${type2class(name)} extends $kstructName {")
    out.inc
  }

  override def classFooter(name: String): Unit = {
    out.dec
    out.puts("}")
  }

  def namespaceHeader(name: List[String]): Unit = {
    out.puts("// deno-lint-ignore no-namespace")
    out.puts(s"export namespace ${type2class(name.last)} {")
    out.inc
  }

  def namespaceAlias(cls: ClassSpec): Unit = {
    out.puts(s"export type ${type2class(cls.name.last)} = InstanceType<typeof ${types2class(cls.name)}>")
  }

  def namespaceFooter(name: List[String]): Unit = {
    out.dec
    out.puts("}")
  }

  override def classConstructorHeader(name: String, parentType: DataType, rootClassName: String, isHybrid: Boolean, params: List[ParamDefSpec]): Unit = {
    if (config.readStoresPos) {
      out.puts("public _debug!: IDebug;")
    }

    typeProvider.nowClass.meta.endian match {
      case Some(_: CalcEndian) | Some(InheritedEndian) =>
        out.puts(s"protected ${_privateMemberName(EndianIdentifier)}!: boolean;")
        out.puts(s"public get ${publicMemberName(EndianIdentifier)}(): boolean { return ${privateMemberName(EndianIdentifier)} };")
      case _ =>
        // no _is_le variable
    }

    val pEndian = paramName(EndianIdentifier)
    val endianSuffix = if (isHybrid) s", $pEndian: boolean" else ""

    val paramsList = Utils.join(params.map((p) =>
      s"${paramName(p.id)}: ${kaitaiType2NativeType(p.dataType)}"
    ), "", ", ", ", ")

    // Parameter names
    val pIo = paramName(IoIdentifier)
    val pParent = paramName(ParentIdentifier)
    val pRoot = paramName(RootIdentifier)

    out.puts(
      s"constructor(" +
        paramsList +
        s"$pIo: ${kaitaiType2NativeType(KaitaiStreamType)}, " +
        s"$pParent: ${kaitaiType2NativeType(parentType)}, " +
        s"$pRoot${if (!isHybrid) "?" else ""}: ${type2class(rootClassName)} | null${if (isHybrid) " | undefined" else ""}" +
        endianSuffix + ") {"
    )
    out.inc

    out.puts(s"super($pIo, $pParent, $pRoot);")

    if (isHybrid)
      handleAssignmentSimple(EndianIdentifier, pEndian)

    params.foreach((p) => handleAssignmentSimple(p.id, paramName(p.id)))

    out.puts

    if (config.readStoresPos) {
      out.puts("this._debug = {};")
    }

  }

  override def classConstructorFooter: Unit = {
    out.dec
    out.puts("}")
  }

  override def runRead(name: List[String]): Unit = {
    out.puts("this.__read();")
  }

  override def runReadCalc(): Unit = {
    out.puts
    out.puts(s"if (${privateMemberName(EndianIdentifier)} === true) {")
    out.inc
    out.puts("this.__readLE();")
    out.dec
    out.puts(s"} else if (${privateMemberName(EndianIdentifier)} === false) {")
    out.inc
    out.puts("this.__readBE();")
    out.dec
    out.puts("} else {")
    out.inc
    out.puts(s"""throw new ${ksErrorName(UndecidedEndiannessError)}("${typeProvider.nowClass.path.mkString("/", "/", "")}");""")
    out.dec
    out.puts("}")
  }

  override def readHeader(endian: Option[FixedEndian], isEmpty: Boolean) = {
    val readAccess = if (!config.autoRead) {
      "public"
    } else {
      "protected"
    }
    val suffix = endian match {
      case Some(e) => Utils.upperUnderscoreCase(e.toSuffix)
      case None => ""
    }
    out.puts(s"$readAccess __read$suffix() {")
    out.inc
  }

  override def readFooter() = {
    out.dec
    out.puts("}")
  }

  override def attributeDeclaration(attrName: Identifier, attrType: DataType, isNullable: Boolean): Unit = {
    val decl = attrName match {
      case IoIdentifier | ParentIdentifier | RootIdentifier | EndianIdentifier => {
        val readAccess = if (!config.autoRead) {
          "public"
        } else {
          "protected"
        }
        s"declare $readAccess ${_privateMemberName(attrName)}"
      }
      case _ => {
        s"private ${_privateMemberName(attrName)}${if (!config.autoRead) "?" else if (!isNullable) "!" else ""}"
      }
    }
    out.puts(s"$decl: ${kaitaiType2NativeType(attrType, false)}${if (isNullable) " | null = null" else ""};")
  }

  override def attributeReader(attrName: Identifier, attrType: DataType, isNullable: Boolean): Unit = {
    val additionalTypes =
      (if (isNullable) " | null" else "") +
      (if (!config.autoRead) " | undefined" else "")
    out.puts(s"public get ${publicMemberName(attrName)}(): ${kaitaiType2NativeType(attrType, false)}$additionalTypes { return ${privateMemberName(attrName)} };")
  }

  override def universalDoc(doc: DocSpec): Unit = {
    // JSDoc docstring style: http://usejsdoc.org/about-getting-started.html
    out.puts
    out.puts( "/**")

    doc.summary.foreach((summary) => out.putsLines(" * ", summary))

    // http://usejsdoc.org/tags-see.html
    doc.ref.foreach {
      case TextRef(text) =>
        out.putsLines(" * ", s"@see $text")
      case UrlRef(url, text) =>
        out.putsLines(" * ", s"@see {@link $url|$text}")
    }

    out.puts( " */")
  }

  override def attrParseHybrid(leProc: () => Unit, beProc: () => Unit): Unit = {
    out.puts(s"if (${privateMemberName(EndianIdentifier)}) {")
    out.inc
    leProc()
    out.dec
    out.puts("} else {")
    out.inc
    beProc()
    out.dec
    out.puts("}")
  }

  override def attrFixedContentsParse(attrName: Identifier, contents: String): Unit = {
    out.puts(s"${privateMemberName(attrName)} = " +
      s"$normalIO.ensureFixedContents($contents);")
  }

  override def attrProcess(proc: ProcessExpr, varSrc: Identifier, varDest: Identifier, rep: RepeatSpec): Unit = {
    val srcExpr = getRawIdExpr(varSrc, rep)

    val expr = proc match {
      case ProcessXor(xorValue) =>
        val procName = translator.detectType(xorValue) match {
          case _: IntType => "processXorOne"
          case _: BytesType => "processXorMany"
        }
        s"${kaitaiType2NativeType(KaitaiStreamType)}.$procName($srcExpr, ${expression(xorValue)})"
      case ProcessZlib =>
        s"${kaitaiType2NativeType(KaitaiStreamType)}.processZlib($srcExpr)"
      case ProcessRotate(isLeft, rotValue) =>
        val expr = if (isLeft) {
          expression(rotValue)
        } else {
          s"8 - (${expression(rotValue)})"
        }
        s"${kaitaiType2NativeType(KaitaiStreamType)}.processRotateLeft($srcExpr, $expr, 1)"
      case ProcessCustom(name, args) =>
        val nameInit = name.init
        val pkgName = if (nameInit.isEmpty) "" else nameInit.mkString("-") + "/"
        val procClass = type2class(name.last)

        importList.add(s"$pkgName$procClass")

        out.puts(s"let _process = new $procClass(${args.map(expression).mkString(", ")});")
        s"_process.decode($srcExpr)"
    }
    handleAssignment(varDest, expr, rep, false)
  }

  override def allocateIO(id: Identifier, rep: RepeatSpec): String = {
    val ioId = IoStorageIdentifier(id)

    val args = rep match {
      case RepeatUntil(_) => translator.doName(Identifier.ITERATOR2)
      case _ => getRawIdExpr(id, rep)
    }

    val newStream = s"new $kstreamName($args)"

    val ioName = rep match {
      case NoRepeat =>
        val localIO = idToStr(id)
        out.puts(s"const $localIO = $newStream;")
        privateMemberName(ioId)
        localIO
      case _ =>
        val localIO = idToStr(id)
        out.puts(s"const $localIO = $newStream;")
        out.puts(s"${privateMemberName(ioId)}.push($localIO);")
        localIO
    }

    ioName
  }

  def getRawIdExpr(varName: Identifier, rep: RepeatSpec): String = {
    val memberName = s"${privateMemberName(varName)}"
    rep match {
      case NoRepeat => memberName
      case RepeatExpr(_) => s"$memberName[${translator.doLocalName(Identifier.INDEX)}]"
      case _ => s"$memberName[$memberName.length - 1]"
    }
  }

  override def useIO(ioEx: expr): String = {
    out.puts(s"let io = ${expression(ioEx)};")
    "io"
  }

  override def pushPos(io: String): Unit =
    out.puts(s"let _pos = $io.pos;")

  override def seek(io: String, pos: Ast.expr): Unit =
    out.puts(s"$io.seek(${expression(pos)});")

  override def popPos(io: String): Unit =
    out.puts(s"$io.seek(_pos);")

  override def alignToByte(io: String): Unit =
    out.puts(s"$io.alignToByte();")

  override def attrDebugStart(attrId: Identifier, attrType: DataType, io: Option[String], rep: RepeatSpec): Unit = {
    if (!attrDebugNeeded(attrId))
      return

    val debugName = attrDebugName(attrId, rep, false)

    val ioProps = io match {
      case None => ""
      case Some(x) => s"start: $x.pos, ioOffset: $x.byteOffset"
    }

    val enumNameProps = attrType match {
      case t: EnumType => s"""enumName: \"${types2class(t.enumSpec.get.name)}\""""
      case _ => ""
    }

    out.puts(s"$debugName = { $ioProps${if (ioProps != "" && enumNameProps != "") ", " else ""}$enumNameProps };")
  }

  override def attrDebugEnd(attrId: Identifier, attrType: DataType, io: String, rep: RepeatSpec): Unit = {
    if (!attrDebugNeeded(attrId))
      return
    val debugName = attrDebugName(attrId, rep, true)

    out.puts(s"$debugName.end = $io.pos;")
  }

  override def condIfHeader(expr: expr): Unit = {
    out.puts(s"if (${expression(expr)}) {")
    out.inc
  }

  override def condIfFooter(expr: expr): Unit = {
    out.dec
    out.puts("}")
  }

  override def condRepeatCommonInit(id: Identifier, dataType: DataType, needRaw: NeedRaw): Unit = {
    out.puts(s"${privateMemberName(id)} = [];")
    if (config.readStoresPos)
      out.puts(s"this._debug.${idToStr(id)}.arr = [];")
  }

  override def condRepeatEosHeader(id: Identifier, io: String, dataType: DataType): Unit = {
    val index = translator.doLocalName(Identifier.INDEX)
    out.puts(s"for (let $index = 0; !$io.is_eof; $index++) {")
    out.inc
  }

  override def handleAssignmentRepeatEos(id: Identifier, expr: String): Unit = {
    out.puts(s"${privateMemberName(id)}.push($expr);")
  }

  override def condRepeatEosFooter: Unit = {
    out.dec
    out.puts("}")
  }

  override def condRepeatExprHeader(id: Identifier, io: String, dataType: DataType, repeatExpr: expr): Unit = {
    val index= translator.doLocalName(Identifier.INDEX)
    out.puts(s"for (let $index = 0; $index < ${expression(repeatExpr)}; $index++) {")
    out.inc
  }

  override def handleAssignmentRepeatExpr(id: Identifier, expr: String): Unit =
    handleAssignmentRepeatEos(id, expr)

  override def condRepeatExprFooter: Unit = {
    out.dec
    out.puts("}")
  }

  override def condRepeatUntilHeader(id: Identifier, io: String, dataType: DataType, untilExpr: expr): Unit = {
    val index = translator.doLocalName(Identifier.INDEX)
    out.puts(s"for (let $index = 0;;) {")
    out.inc
  }

  override def handleAssignmentRepeatUntil(id: Identifier, expr: String, isRaw: Boolean): Unit = {
    val tmpName = translator.doLocalName(if (isRaw) Identifier.ITERATOR2 else Identifier.ITERATOR)
    out.puts(s"let $tmpName = $expr;")
    out.puts(s"${privateMemberName(id)}.push($tmpName);")
  }

  override def condRepeatUntilFooter(id: Identifier, io: String, dataType: DataType, untilExpr: expr): Unit = {
    typeProvider._currentIteratorType = Some(dataType)
    out.puts(s"if (!(${expression(untilExpr)})) break;")
    out.dec
    out.puts("}")
  }

  override def handleAssignmentSimple(id: Identifier, expr: String): Unit = {
    out.puts(s"${privateMemberName(id)} = $expr;")
  }

  override def handleAssignmentTempVar(dataType: DataType, id: String, expr: String): Unit =
    out.puts(s"let $id = $expr;")

  override def parseExpr(dataType: DataType, assignType: DataType, io: String, defEndian: Option[FixedEndian]): String = {
    dataType match {
      case Int1Type(signed) =>
        s"$io.read${if (signed) "Ui" else "I"}nt(1)"
      case IntMultiType(signed, width, endian) =>
        s"$io.read${if (signed) "Ui" else "I"}nt(${width.width}${endian.orElse(defEndian).getOrElse(BigEndian) match {
          case LittleEndian => ", true"
          case BigEndian => ""
        }})"
      case FloatMultiType(width, endian) =>
        s"$io.readFloat(${width.width}${endian.orElse(defEndian).getOrElse(BigEndian) match {
          case LittleEndian => ", true"
          case BigEndian => ""
        }})"
      case blt: BytesLimitType =>
        s"$io.readBytes(${expression(blt.size)})"
      case _: BytesEosType =>
        s"$io.readBytesFull()"
      case BytesTerminatedType(terminator, include, consume, eosError, _) =>
        s"$io.readBytesTerm($terminator, $include, $consume, $eosError)"
      case BitsType1(bitEndian) =>
        s"$io.readBitsInt${Utils.upperCamelCase(bitEndian.toSuffix)}(1) != 0"
      case BitsType(width: Int, bitEndian) =>
        s"$io.readBitsInt${Utils.upperCamelCase(bitEndian.toSuffix)}($width)"
      case t: UserType =>
        val parent = t.forcedParent match {
          case Some(USER_TYPE_NO_PARENT) => "null"
          case Some(fp) => translator.translate(fp)
          case None => "this"
        }
        val root = if (t.isOpaque || t.classSpec.get.name.head != typeProvider.nowClass.name.head) "null" else "this._root"
        val addEndian = t.classSpec.get.meta.endian match {
          case Some(InheritedEndian) => ", this._is_le"
          case _ => ""
        }
        val addParams = Utils.join(t.classSpec.get.params.zip(t.args).map{
          case (pds, arg) => {
            println(pds)
            println(arg)
            println(translator.detectType(arg))
            //TODO check against param
            (pds.dataType, translator.detectType(arg)) match {
              case (IntMultiType(_, Width8, _), CalcIntType) =>
                translator.bigIntTranslate(arg)
              case (IntMultiType(_, paramWidth, _), IntMultiType(_, argWidth, _)) => (paramWidth, argWidth) match {
                case (Width8, _) => translator.bigIntTranslate(arg)
                case (_, Width8) => s"${kaitaiType2NativeType(KaitaiStreamType)}.castBigInt(${translator.translate(arg)})"
                case _ => translator.translate(arg)
              }
              case _ => translator.translate(arg)
            }
          }
        }, "", ", ", ", ")
        s"new ${types2class(t.classSpec.get.name)}($addParams$io, $parent, $root$addEndian)"
    }
  }

  override def createSubstreamFixedSize(id: Identifier, sizeExpr: Ast.expr, io: String): String = {
    val ioName = idToStr(IoStorageIdentifier(id))
    handleAssignmentTempVar(KaitaiStreamType, ioName, s"$io.substream(${translator.translate(sizeExpr)})")
    ioName
  }

  override def extraRawAttrForUserTypeFromBytes(id: Identifier, ut: UserTypeFromBytes, condSpec: ConditionalSpec): List[AttrSpec] = {
    if (config.zeroCopySubstream) {
      ut.bytes match {
        case BytesLimitType(sizeExpr, None, _, None, None) =>
          // substream will be used, no need for store raws
          List()
        case _ =>
          // buffered implementation will be used, fall back to raw storage
          super.extraRawAttrForUserTypeFromBytes(id, ut, condSpec)
      }
    } else {
      // zero-copy streams disabled, fall back to raw storage
      super.extraRawAttrForUserTypeFromBytes(id, ut, condSpec)
    }
  }

  override def bytesPadTermExpr(expr0: String, padRight: Option[Int], terminator: Option[Int], include: Boolean) = {
    val expr1 = padRight match {
      case Some(padByte) => s"${kaitaiType2NativeType(KaitaiStreamType)}.bytesStripRight($expr0, $padByte)"
      case None => expr0
    }
    val expr2 = terminator match {
      case Some(term) => s"${kaitaiType2NativeType(KaitaiStreamType)}.bytesTerminate($expr1, $term, $include)"
      case None => expr1
    }
    expr2
  }

  override def userTypeDebugRead(id: String, dataType: DataType, assignType: DataType): Unit = {
    val incThis = if (id.startsWith("_t_")) "" else "this."
    out.puts(s"$id.__read();")
  }

  override def switchRequiresIfs(onType: DataType): Boolean = onType match {
    case _: IntType | _: BooleanType | _: EnumType | _: StrType => false
    case _ => true
  }

  //<editor-fold desc="switching: true version">

  override def switchStart(id: Identifier, on: Ast.expr): Unit = {
    out.puts(s"switch (${expression(on)}) {")
    out.inc
  }

  override def switchCaseFirstStart(condition: Ast.expr): Unit =
    switchCaseStart(condition)

  override def switchCaseStart(condition: Ast.expr): Unit = {
      out.puts(s"case ${expression(condition)}: {")
      out.inc
  }

  override def switchCaseEnd(): Unit = {
      out.puts("break;")
      out.dec
      out.puts("}")
  }

  override def switchElseStart(): Unit = {
      out.puts("default: {")
      out.inc
  }

  override def switchEnd(): Unit = {
    out.dec
    out.puts("}")
  }

  //</editor-fold>

  //<editor-fold desc="switching: emulation with ifs">

  val NAME_SWITCH_ON = Ast.expr.Name(Ast.identifier(Identifier.SWITCH_ON))

  override def switchIfStart(id: Identifier, on: Ast.expr, onType: DataType): Unit = {
    out.puts("{")
    out.inc
    out.puts(s"let ${expression(NAME_SWITCH_ON)} = ${expression(on)}")
  }

  private def switchCmpExpr(condition: Ast.expr): String =
    expression(
      Ast.expr.Compare(
        NAME_SWITCH_ON,
        Ast.cmpop.Eq,
        condition
      )
    )

  override def switchIfCaseFirstStart(condition: Ast.expr): Unit = {
    out.puts(s"if (${switchCmpExpr(condition)}) {")
    out.inc
  }

  override def switchIfCaseStart(condition: Ast.expr): Unit = {
    out.puts(s"else if (${switchCmpExpr(condition)}) {")
    out.inc
  }

  override def switchIfCaseEnd(): Unit = {
    out.dec
    out.puts("}")
  }

  override def switchIfElseStart(): Unit = {
    out.puts("else {")
    out.inc
  }

  override def switchIfEnd(): Unit = {
    out.dec
    out.puts("}")
  }

  //</editor-fold>

  override def instanceDeclaration(instName: InstanceIdentifier, attrType: DataType, isNullable: Boolean): Unit = {
    val decl = s"private ${_privateMemberName(instName)}?"
    out.puts(s"$decl: ${kaitaiType2NativeType(attrType, false)}${if (isNullable) " | null" else ""};")
  }

  override def instanceHeader(className: String, instName: InstanceIdentifier, dataType: DataType, isNullable: Boolean): Unit = {
    val additionalTypes =
      (if (isNullable) " | null" else "") +
      (if (!config.autoRead) " | undefined" else "")
    out.puts(s"public get ${publicMemberName(instName)}(): ${kaitaiType2NativeType(dataType, false)}$additionalTypes {")
    out.inc
  }

  override def instanceClear(instName: InstanceIdentifier) = {
    out.puts(s"${privateMemberName(instName)} = undefined;")
  }

  def instanceEnsureNull(instName: InstanceIdentifier) = {
    out.puts(s"if (${privateMemberName(instName)} === undefined)")
    out.inc
    out.puts(s"${privateMemberName(instName)} = null;")
    out.dec
  }

  override def instanceFooter: Unit = {
    out.dec
    out.puts("}")
    out.puts
  }

  def instanceCheckCacheAndReturn(instName: InstanceIdentifier, dataType: DataType): Unit = {
    out.puts(s"if (${privateMemberName(instName)} !== undefined)")
    out.inc
    instanceReturn(instName, dataType)
    out.dec
  }

  override def instanceReturn(instName: InstanceIdentifier, attrType: DataType): Unit = {
    out.puts(s"return ${privateMemberName(instName)}!;")
  }

  override def enumDeclaration(curClass: String, enumName: String, enumColl: Seq[(Long, String)]): Unit = {
    out.puts(s"export enum ${type2class(enumName)} {")
    out.inc

    enumColl.foreach { case (id, label) =>
      out.puts(s"${Utils.upperUnderscoreCase(label)} = ${translator.doIntLiteral(id)},")
    }

    out.dec
    out.puts("}")
  }
  
  override def classToString(toStringExpr: Ast.expr): Unit = {
    out.puts
    out.puts("public toString(): string {")
    out.inc
    out.puts(s"return ${translator.translate(toStringExpr)};")
    out.dec
  }
  
  override def idToStr(id: Identifier): String = TypeScriptCompiler.idToStr(id)

  override def publicMemberName(id: Identifier) = TypeScriptCompiler.publicMemberName(id)

  def _privateMemberName(id: Identifier): String = s"_${idToStr(id)}" + (id match {
    case NamedIdentifier("io" | "parent" | "root") => "_v"
    case _ => ""
  })

  override def privateMemberName(id: Identifier): String = s"this.${_privateMemberName(id)}"

  override def localTemporaryName(id: Identifier): String = s"_t_${idToStr(id)}"

  override def ksErrorName(err: KSError): String = TypeScriptCompiler.ksErrorName(err)

  override def attrValidateExpr(
    attrId: Identifier,
    attrType: DataType,
    checkExpr: Ast.expr,
    err: KSError,
    errArgs: List[Ast.expr]
  ): Unit = {
    val errArgsStr = errArgs.map(translator.translate).mkString(", ")
    out.puts(s"if (!(${translator.translate(checkExpr)})) {")
    out.inc
    out.puts(s"throw new ${ksErrorName(err)}($errArgsStr);")
    out.dec
    out.puts("}")
  }

  private def attrDebugNeeded(attrId: Identifier) = attrId match {
    case _: NamedIdentifier | _: NumberedIdentifier | _: InstanceIdentifier => true
    case _: RawIdentifier | _: SpecialIdentifier => false
  }

  def attrDebugName(attrId: Identifier, rep: RepeatSpec, end: Boolean) = {
    val arrIndexExpr = rep match {
      case NoRepeat => ""
      case _: RepeatExpr => ".arr[i]"
      case RepeatEos | _: RepeatUntil => s".arr[${privateMemberName(attrId)}.length${if (end) " - 1" else ""}]"
    }

    s"this._debug.${idToStr(attrId)}$arrIndexExpr"
  }
}

object TypeScriptCompiler extends LanguageCompilerStatic
  with UpperCamelCaseClasses
  with StreamStructNames
  with ExceptionNames {
  override def getCompiler(
    tp: ClassTypeProvider,
    config: RuntimeConfig
  ): LanguageCompiler = new TypeScriptCompiler(tp, config)

  def kaitaiType2NativeType(attrType: DataType, absolute: Boolean = false): String = {
    attrType match {
      case IntMultiType(_, Width8, _) => "bigint"
      case _: NumericType => "number"

      case BitsType(_, _) => "number"

      case _: BooleanType => "boolean"
      case CalcIntType => "number"
      case CalcFloatType => "number"

      case _: StrType => "string"
      case _: BytesType => "Uint8Array"

      case t: UserType =>
        s"${types2class(t.classSpec match {
          case None => t.name
          case Some(cs) => cs.name
        })}"

      case t: EnumType => types2class(t.enumSpec.get.name)

      case at: ArrayType =>
        s"(${kaitaiType2NativeType(at.elType, absolute)})[]"

      case CalcArrayType(inType) => s"(${kaitaiType2NativeType(inType, absolute)})[]"

      case AnyType => "any"

      case KaitaiStreamType => s"$kstreamName"
      case KaitaiStructType | CalcKaitaiStructType => s"$kstructName"

      // unfolds and removes duplicates by converting to set
      case SwitchType(_, cases, _) => cases.map(kv => kaitaiType2NativeType(kv._2, false)).toSet.mkString(" | ")
    }
  }

  def idToStr(id: Identifier): String = {
    id match {
      case SpecialIdentifier(name) => name
      case NamedIdentifier(name) => Utils.lowerCamelCase(name)
      case NumberedIdentifier(idx) => s"_${NumberedIdentifier.TEMPLATE}$idx"
      case InstanceIdentifier(name) => s"_m_${Utils.lowerCamelCase(name)}"
      case RawIdentifier(innerId) => "_raw_" + idToStr(innerId)
      case IoStorageIdentifier(inner) => s"_io_${idToStr(inner)}"
    }
  }

  def publicMemberName(id: Identifier): String =
    id match {
      case InstanceIdentifier(name) => Utils.lowerCamelCase(name)
      case _ => idToStr(id)
    }

  override def kstreamName: String = "KaitaiStream"

  override def kstructName: String = "KaitaiStruct"

  override def ksErrorName(err: KSError): String = err match {
    case _ => s"$kstructName.Errors.${err.name}"
  }

  def types2class(types: List[String]): String = types.map(type2class).mkString(".")
}
