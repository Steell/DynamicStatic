using System;
using System.Collections.Generic;
using System.Linq;
using System.Text;
using DynamicStatic;
using NUnit.Framework;

namespace DynamicStaticTests
{
    [TestFixture]
    public class OverloadTests
    {
        [Test]
        public void OverloadCall()
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
        public void OverloadDefinition()
        {
            Assert.AreEqual(
                DS.type2str(DS.notType),
                DS.type2str(DS.type_check(DS.notExpr)));
        }

        [Test]
        public void RecursiveOverloadDefinition()
        {
            Assert.AreEqual(
                "(List<{'a|'b}> -> ((('a -> True)+('b -> False)) -> List<'a>))",
                DS.type2str(DS.type_check(DS.filter)));
        }
    }
}
