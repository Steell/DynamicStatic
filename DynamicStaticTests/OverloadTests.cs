using System;
using System.Collections.Generic;
using System.Linq;
using System.Text;
using DynamicStatic;
using Microsoft.FSharp.Collections;
using NUnit.Framework;

namespace DynamicStaticTests
{
    [TestFixture]
    public class OverloadTests
    {
        [Test]
        public void NotCall_1Match()
        {
            var notCall = DS.TypeExpression.NewCall(
                DS.TypeExpression.NewType_E(DS.notType),
                DS.TypeExpression.NewType_E(DS.Type.True));

            Assert.AreEqual("False", DS.type2str(DS.type_check(notCall)));

            var notCall2 = DS.TypeExpression.NewCall(
                DS.TypeExpression.NewType_E(DS.notType),
                DS.TypeExpression.NewType_E(DS.Type.False));

            Assert.AreEqual("True", DS.type2str(DS.type_check(notCall2)));
        }

        [Test]
        public void NotCall_2Match()
        {
            var notCall3 = DS.TypeExpression.NewCall(
                DS.TypeExpression.NewType_E(DS.notType),
                DS.TypeExpression.NewType_E(
                    DS.Type.NewUnion(
                        SetModule.OfSeq(new List<DS.Type> { DS.Type.True, DS.Type.False }))));

            Assert.AreEqual("{True|False}", DS.type2str(DS.type_check(notCall3)));
        }

        [Test]
        public void NotDefinition()
        {
            Assert.AreEqual(
                DS.type2str(DS.notType),
                DS.type2str(DS.type_check(DS.notExpr)));
        }

        [Test]
        public void FilterDefinition()
        {
            var actual = DS.type2str(DS.type_check(DS.filter));

            Assert.AreEqual(
                "(List<{'a|'b}> -> ((('a -> True)+('b -> False)) -> List<'a>))",
                actual);
        }
    }
}
